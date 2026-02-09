#lang racket

(provide spawn-compile-one
         compile-all-parallel
	 all-deps-have-reached?
	 compile-headers
	 compile-cpp-to-object
	 link-and-build-bin
	 run-cmd)

(require "utils.rkt"
	 racket/system
	 racket/hash
	 racket/runtime-path)


(define null-device-path
  (if (eq? (system-type) 'windows) "NUL" "/dev/null"))


;; Spins up a new process to handle a small set of files/X folders 
(define (spawn-compile-one folder-names)
  (thread
   (lambda ()
     (define rkt-path 
       (string-replace
	(path->string (normalize-path "rkt/compile.rkt"))
	"\\" "/"))

     (define cmd 
       (format "(require (file \"~a\"))~a"
	       rkt-path ;; This worker handles a list of folders
	       (foldl string-append ""
		      (map (lambda (name)
			     (format "(compile-one \"~a\")" name))
			   folder-names))))
     
     (run-cmd (find-executable-path "racket") "-e" cmd))))


(define (get-files-ext dir ext)
  ;; Convert the extension string to bytes for comparison
  (define ext-bytes (string->bytes/utf-8 ext))
  
  (for/list ([item (in-list (directory-list dir))]
             ;; Check if it has the extension AND is actually a file
             #:when (and (equal? (filename-extension item) ext-bytes)
                         (file-exists? (build-path dir item))))
	    (build-path dir item)))

(define (all-deps-have-reached? build-root-path ext)
  ;; Returns true only if every file subdir has reached ext status
  (define entries (directory-list build-root-path))
  (define subdirs 
    (filter (lambda (p) (directory-exists? (build-path build-root-path p))) 
            entries))
  (andmap 
   (lambda (subdir)
     (define full-subdir-path (build-path build-root-path subdir))
     (ormap 
      (lambda (file) (path-has-extension? file ext)) 
      (directory-list full-subdir-path)))
   subdirs))


(define (compile-headers build-root)
  (define full-header
    (foldl string-append
	   ""
           (for/list ([entry (in-list (directory-list build-root))]
                      #:when (directory-exists? (build-path build-root entry)))
		     (define subdir (build-path build-root entry))
		     ;; Find all .h files in this specific subdirectory
		     (define h-files 
		       (filter (lambda (f) (path-has-extension? f ".h"))
			       (directory-list subdir)))
		     ;; Read and concat files within this subdir
		     (apply string-append 
			    (map (lambda (h) (file->string (build-path subdir h)))
				 h-files)))))
  (with-output-to-file
      (build-path build-root "header.h")
    (lambda () (newline) (display full-header) (newline))
    #:exists 'append))


(define (compile-all-parallel)
  (define files-root "/tmp/ti/files")
  (define build-root "/tmp/ti/build")
  (when (directory-exists? files-root)
    (define dirlst (directory-list files-root #:build? #f))
    (define groups ;; Subfolders can be handled in parallel
      (let ([i 0]) ;; Put into 7 partitions:
	(group-by (λ (_) (begin0 i (set! i (modulo (add1 i) 7))))
		  dirlst))) ;; Spin up 7 worker processes:
    (for/list ([group (in-list groups)])
	      (spawn-compile-one group))))


(define (run-cmd prog . args)
  (define log-port (open-output-file
		    (build-path "/tmp/ti/error.log")
		    #:exists 'append))
  (define stdin-port (open-input-file null-device-path))
  (define-values (sp out in err)
    (apply subprocess log-port stdin-port log-port prog args))
  (close-output-port log-port)
  (close-input-port stdin-port)
  (subprocess-wait sp)
  (unless (zero? (subprocess-status sp))
    (error (format "Build command failed: ~a ~a" prog args))))


(define (compile-cpp-to-object cpp-path header-path obj-path)
  (thread
   (lambda ()
     (define cxx-path (or (find-executable-path "clang++") 
			  (find-executable-path "c++")))
     (unless cxx-path (error "Error: clang++ not found in PATH."))
     (run-cmd cxx-path
              "-c" cpp-path
              "-o" obj-path
              "-include" header-path 
              "-std=c++20"
	      "-g"  "-DDEBUG"
              "-march=native"
              "-flto=thin" 
              "-ferror-limit=3")
     ;; Copy the .o file into the build folder
     (copy-file obj-path
		(match (explode-path obj-path)
		  [`(,front ... ,_ ,file)
		   (apply build-path `(,@front ,file))])
		#t))))


(define (compile-objects-to-bin project-path
				[out-path "/tmp/ti/out.bin"])
  (define cxx-path (or (find-executable-path "clang++") 
                       (find-executable-path "c++")))
  (unless cxx-path (error "Error: clang++ not found in PATH."))
  (define obj-files
    (for/list ([f (in-list (directory-list project-path))]
               #:when (path-has-extension? f ".o"))
      (path->string (build-path project-path f))))
  ;; Todo: more carefully check all .o files compiled successfully?
  (when (null? obj-files)
    (error (format "No .o files found in ~a" project-path)))
  (apply run-cmd
	 cxx-path
	 "-lgc"
	 "-lgmp"
	 "-flto=thin"
	 "-fuse-ld=lld"
         "-o" out-path
	 obj-files))


(define (link-and-build-bin project-path)
  (define local-bin (build-path project-path "out.bin"))
  (define global-bin "/tmp/ti/out.bin")

  (compile-objects-to-bin project-path (path->string local-bin))

  (when (file-exists? global-bin)
    (delete-file global-bin))
  
  (copy-file local-bin global-bin)
  
  (displayln (format "Build successful: ~a" global-bin)))


