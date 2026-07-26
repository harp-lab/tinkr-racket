#lang racket


(provide setup-build-workspace
	 read-all-inline
	 build-project
   wait-on-all-threads
   (struct-out build-options))


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

;; Cache entries are keyed by source AND compiler version: if any rkt/
;; source changes, every cache dir name changes and old entries are
;; never consulted again (no rm -rf /tmp/ti needed after compiler edits).
(define compiler-salt
  (let ([rkt-files (sort (for/list ([f (in-list (directory-list this-dir #:build? #t))]
                                    #:when (path-has-extension? f ".rkt"))
                           (path->string f))
                         string<?)])
    (substring (sha1 (open-input-bytes
                      (apply bytes-append (map file->bytes rkt-files))))
               0 6)))

(define all-inline-file (format "/tmp/ti/all_~a.inline" compiler-salt))


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


;; Returns a list of include edges for the module at `path`:
;;   ((<include-string> (clause ...) ...) ...)
;; in textual order. Only .ti includes are edges.
(define (extract-include-edges path)
  (define ast
    (strip-prov (match (parse-file path) [`(module ,_ ,_ ,body) body] [x x])))
  (let loop ([e ast])
    (match e
      [`(include (const ,p) ,cls ... ,body)
       (if (and (string? p) (string-suffix? p ".ti"))
           (cons `(,p ,@cls) (loop body))
           (loop body))]
      [(? list? l) (append-map loop l)]
      [_ '()])))

(define (extract-includes path)
  (map car (extract-include-edges path)))


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


;; Build-dir stems become C identifier material (mv_<dir>__<name> symbols
;; embed them), so only [A-Za-z0-9_] may pass through. '.' keeps the
;; readable '_' convention; anything else (hyphens, spaces, ...) gets the
;; same hex escape escape-id-for-C uses.
(define (sanitize-dir-stem name)
  (apply string-append
         (for/list ([c (in-string name)])
           (cond [(or (char-alphabetic? c) (char-numeric? c) (eqv? c #\_))
                  (string c)]
                 [(eqv? c #\.) "_"]
                 [else (string-append "_" (~r (char->integer c) #:base 16
                                              #:min-width 5 #:pad-string "0"))]))))

(define (install-to-files path)

  (define hash (hash-content path))
  (define name (path->string (file-name-from-path path)))
  (define dir-name (format "~a_~a~a" (sanitize-dir-stem name) hash compiler-salt))
  (define files-dir (build-path "/tmp/ti/files" dir-name))
  
  (unless (directory-exists? files-dir)
    ;; If installation fails partway (e.g. a load error in the module),
    ;; remove the half-made dir so it cannot poison later builds.
    (with-handlers ([exn:fail? (lambda (e)
                                 (delete-directory/files files-dir #:must-exist? #f)
                                 (raise e))])
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
				     (list->set inline))))))))
  
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
  (define dir-names (make-hash)) ;; abs path -> build dir name
  (for ([f (in-list all-files)])
       (define-values (dir-name files-path) (install-to-files f))
       (hash-set! dir-names f dir-name)
       (make-file-or-directory-link files-path (build-path build-root dir-name)))

  ;; Record the include DAG (with clauses) for the linker:
  ;;   (prelude <base-dir>)
  ;;   (root <root-dir>)
  ;;   (modules (<dir> (<target-dir> (clause ...) ...) ...) ...)
  (define graph
    (for/list ([f (in-list all-files)])
      `(,(hash-ref dir-names f)
        ,@(for/list ([edge (in-list (extract-include-edges f))])
            (match-define (cons inc-str cls) edge)
            `(,(hash-ref dir-names (resolve-include f inc-str)) ,@cls)))))
  (with-output-to-file (build-path build-root "graph.rktd")
    #:exists 'replace
    (lambda ()
      (write `((prelude ,(hash-ref dir-names base-ti-path))
               (root ,root-dir-name)
               (modules ,@graph)))))

  (path->string build-root))


(define (wait-on-all-threads lst)
  (define threads (filter thread? lst))
  (let loop ([running threads])
    (unless (null? running)
      (define result (sync (apply choice-evt build-error-chan running)))
      (if (exn:fail? result)
          (error 'build-failed "Worker thread crashed:\n~a" (exn-message result))
          (loop (remove result running))))))


(define (build-project path options)

  (define project (setup-build-workspace path))

  (set-options! options)

  ;; Launch ~7 independent racket processes
  ;; These tackle the initial per-module compilation
  (define ti-comp-threads (compile-all-parallel project (build-options-separate-logs? options)))
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




