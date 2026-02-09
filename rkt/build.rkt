#lang racket


(provide setup-build-workspace
	 read-all-inline
	 build-project)


(require "parser.rkt"
	 "load-module.rkt"
	 "link.rkt"
	 "build-process.rkt"
	 racket/system
	 racket/hash
         file/sha1 
         racket/runtime-path
         racket/list)


(define-runtime-path this-dir ".")
(define all-inline-file "/tmp/ti/all.inline")


;; Searches nearby folders for std/base.ti
(define std-root
  (let loop ([p (simplify-path (path->complete-path this-dir))] [d 0])
    (cond [(> d 3) (error "Could not locate std/base.ti")]
          [(file-exists? (build-path p "std/base.ti"))
	   (simplify-path (build-path p "std"))]
          [(for/or ([sub (directory-list p #:build? #t)])
		   (and (directory-exists? sub) 
			(file-exists? (build-path sub "std/base.ti"))
			(simplify-path (build-path sub "std"))))]
          [else (loop (build-path p "..") (+ d 1))])))


(define base-ti-path (simplify-path (build-path std-root "base.ti")))


(define (resolve-include current-path inc-str)
  (define relative (build-path (path-only current-path) inc-str))
  (define standard (build-path std-root inc-str))
  (cond [(file-exists? relative) (simplify-path relative)]
        [(file-exists? standard) (simplify-path standard)]
        [else (error "Cannot resolve:" inc-str "from" current-path)]))


(define (extract-includes path)
  (define ast (match (parse-file path) [`(module ,_ ,_ ,body) body] [x x]))
  (let loop ([e ast])
    (match e
      [`(syn ,_ include (syn ,_ const ,p) ,body)
       (if (string-suffix? p ".ti") 
           (cons p (loop body)) 
           (loop body))]
      [(? list? l) (append-map loop l)]
      [_ '()])))


(define (collect-deps root-path)
  (define seen (mutable-set))
  (let loop ([path (simplify-path (path->complete-path root-path))])
    (unless (set-member? seen path)
      (set-add! seen path)
      (for ([inc (in-list (extract-includes path))])
           (loop (resolve-include path inc)))))
  
  ;; Ensure base.ti is visited
  (unless (set-member? seen base-ti-path)
    (let loop ([path base-ti-path])
      (unless (set-member? seen path)
        (set-add! seen path)
        (for ([inc (in-list (extract-includes path))])
             (loop (resolve-include path inc))))))
          
  (set->list seen))


(define (hash-content path)
  (define ast (strip-prov (parse-file path)))
  ;; Write AST structure to bytes for canonicalization
  (define canon (with-output-to-bytes (lambda () (write ast))))
  ;; sha1 returns a 40-char hex string
  (define hex (sha1 (open-input-bytes canon)))
  (substring hex 0 6))


(define (read-all-inline)
  ;; Pretty kludgy, we just update a global file with inline blessed
  (if (file-exists? all-inline-file)
      (with-input-from-file all-inline-file read)
      '()))


(define (install-to-files path)
  
  (define hash (hash-content path))
  (define name (path->string (file-name-from-path path)))
  (define dir-name (format "~a_~a" (string-replace name "." "_") hash))
  (define files-dir (build-path "/tmp/ti/files" dir-name))
  
  (unless (directory-exists? files-dir)
    (make-directory* files-dir)
    (copy-file path (build-path files-dir name) #t)
    (match-define `(module ,_ ,bless ,inline
			   ,blessed ,lets ,defs)
		  (load-module path))
    ;; Pretty kludgy, we just update a global file with inline blessed
    (define old-inline (read-all-inline))
    (with-output-to-file
	all-inline-file
      #:exists 'replace
      (lambda ()
	(write (set->list (set-union (list->set old-inline)
				     (list->set inline)))))))
  
  (values dir-name files-dir))


(define (setup-build-workspace root-path)
  (define root-abs (simplify-path (path->complete-path root-path)))
  (define all-files (collect-deps root-abs))
  
  ;; Install root first to get the build directory name
  (define-values (root-dir-name _) (install-to-files root-abs))
  (define build-root (build-path "/tmp/ti/build" root-dir-name))
  
  ;; Reset and create build directory
  (when (directory-exists? build-root)
    (delete-directory/files build-root))
  (make-directory* build-root)
  (copy-file (build-path std-root "header.h")
	     (build-path build-root "header.h"))
  (display-to-file "" "/tmp/ti/error.log" #:exists 'append)
  
  ;; Symlink all dependencies into the flattened build folder
  (for ([f (in-list all-files)])
       (define-values (dir-name files-path) (install-to-files f))
       (make-file-or-directory-link files-path (build-path build-root dir-name)))
  
  (path->string build-root))


(define (wait-on-all-threads lst)
  (for ([t (in-list lst)])
       (when (thread? t) (thread-wait t))))


(define (build-project path)

  (define project (setup-build-workspace path))

  ;; Cleanup stale parts of the build
  (run-cmd (find-executable-path "rm") "-f"
	   "/tmp/ti/build/*/*/*.cpp"
	   "/tmp/ti/build/*/*/*.h"
	   "/tmp/ti/build/*/*/*.core"
	   "/tmp/ti/build/*/*/*.bl"
	   "/tmp/ti/build/*/*/*.o")  

  ;; Launch ~7 independent racket processes
  ;; These tackle the initial per-module compilation
  (define ti-comp-threads (compile-all-parallel))
  (wait-on-all-threads ti-comp-threads)

  ;; Compile an init module for globals
  (compile-link-module project)

  ;; Wait for these threads to finish their .h files
  (for ([(i) (in-list (range 45))]
	#:break (all-deps-have-reached? project ".h")) 
       (sleep 0.5))

  ;; Compile all headers and add to build/X/header.h
  (compile-headers project)

  ;; Compile all .o files (in parallel subprocesses)
  (define cpp-comp-threads
    (for/list ([(entry) (in-directory project)]
               #:when (directory-exists? entry))
	      (define name
		(for/first ([(file) (in-directory entry)]
			    #:when (path-has-extension? file ".cpp"))
			   (path->string (path-replace-extension
					  (file-name-from-path file)
					  ""))))
	      (if name
		  (compile-cpp-to-object
		   (path->string (build-path entry (format "~a.cpp" name)))
		   (path->string (build-path project "header.h"))
		   (path->string (build-path entry (format "~a.o" name))))
		  #f)))

  ;; Wait for all threads to finish
  (wait-on-all-threads cpp-comp-threads)

  ;; Build final executable to /tmp/ti/out.bin
  (link-and-build-bin project)
  
  (void))




