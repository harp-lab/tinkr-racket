#lang racket

(provide spawn-compile-one
         compile-all-parallel
         all-deps-have-reached?
         compile-headers
         compile-cpp-to-object
         link-and-build-bin
         build-error-chan
         run-cmd
         set-options!
         (struct-out build-options))


(require "utils.rkt"
	 racket/system
	 racket/hash
   racket/runtime-path
   racket/string)


(struct build-options
  [debug?
   separate-logs?
   lto?
   opt?
   no-strict-aliasing?
   show-flags?
   print-cmds?
   c-compiler-flags
   c-linker-flags]
  #:transparent)

;; A helper human-readable tag for the error file produced
;; by run-cmd. Can be set!ed before calling run-cmd.
(define error-file-tag "")

(define options #f)
(define (set-options! opts)
  (set! options opts))

(define null-device-path
  (if (eq? (system-type) 'windows) "NUL" "/dev/null"))



;; Channel to catch and bubble up thread crashes
(define build-error-chan (make-channel))

;; Spawns a thread that reports exceptions back to the main thread
(define (spawn-safe thunk)
  (thread
   (lambda ()
     (with-handlers ([exn:fail? (lambda (exn) (channel-put build-error-chan exn))])
       (thunk)))))

;; Spins up a new process to handle a small set of files/X folders 
(define (spawn-compile-one folder-names separate-logs)
  (spawn-safe
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
     
     (when separate-logs
      (set! error-file-tag (car folder-names))) ; Seperates the error files by thread if enabled
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


;; Compiles only the modules of the given build (its symlinked subdirs) —
;; NOT everything ever cached under /tmp/ti/files: a stale or broken source
;; elsewhere in the cache must not affect (or slow down) unrelated builds.
(define (compile-all-parallel project [separate-logs #f])
  (define dirlst
    (for/list ([entry (in-list (directory-list project))]
               #:when (directory-exists? (build-path project entry)))
      entry))
  (define groups ;; Subfolders can be handled in parallel
    (let ([i 0]) ;; Put into 7 partitions:
      (group-by (λ (_) (begin0 i (set! i (modulo (add1 i) 7))))
                dirlst))) ;; Spin up 7 worker processes:
  (for/list ([group (in-list groups)])
            (spawn-compile-one group separate-logs)))


(define (run-cmd prog . args)
  (when (build-options-print-cmds? options)
    (displayln (format "~a ~a" prog (string-join args " "))))
  
  (define log-port (open-output-file
        (build-path (format "/tmp/ti/error~a.log" error-file-tag))
		    #:exists 'append))
  (define stdin-port (open-input-file null-device-path))
  (define-values (sp out in err)
    (apply subprocess log-port stdin-port log-port prog args))
  (close-output-port log-port)
  (close-input-port stdin-port)
  (subprocess-wait sp)
  (unless (zero? (subprocess-status sp))
    (error (format "Build command failed: ~a ~a" prog args))))

;; Finds the path to a C++ compiler. Returns a tuple containing both the
;; type of compiler (clang++ or c++) and path.
(define (find-cxx-path)
  (define clang-attempt (find-executable-path "clang++"))
  (cond
    [clang-attempt `(clang++ ,clang-attempt)]
    [else
      (define c++-attempt (find-executable-path "c++"))
      (unless c++-attempt (error "Error: neither clang++ nor c++ not found in PATH."))
      `(c++ ,c++-attempt)]))

(define (compile-cpp-to-object cpp-path header-path obj-path)
  (spawn-safe
   (lambda ()
     (match-define `(,cxx-type ,cxx-path) (find-cxx-path))
     (define clang? (equal? cxx-type 'clang++))

     (define compile-flags
       (append
         (list "-g" "-march=native" "-w")
         (if clang? (list "-ferror-limit=3") (list "-fmax-errors=3"))
         (if (and (build-options-lto? options) clang?) (list "-flto=thin") '())
         (if (build-options-opt? options) (list "-O2") '())
         (if (build-options-no-strict-aliasing? options) (list "-fno-strict-aliasing") '())
         (if (build-options-debug? options) (list "-DDEBUG") '())
         (build-options-c-compiler-flags options)))
     
     (when (build-options-show-flags? options)
       (displayln (format "CXX compile flags: ~a" compile-flags)))

     (apply run-cmd
            (append
              (list cxx-path
                "-c" cpp-path
                "-o" obj-path
                "-include" header-path
                "-std=c++20")
              compile-flags))
     ;; Copy the .o file into the build folder using the hashed dir name
     (copy-file obj-path
        (match (explode-path obj-path)
          [`(,front ... ,dir ,file)
           (apply build-path `(,@front ,(format "~a.o" (path->string dir))))])
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

  (define link-flags
    (append
        (if (build-options-lto? options)
            (list "-lgc" "-lgmp" "-flto=thin" "-fuse-ld=lld")
            (list "-lgc" "-lgmp"))
        (if (build-options-opt? options) (list "-O2") '())
        (if (build-options-no-strict-aliasing? options) (list "-fno-strict-aliasing") '())
        (build-options-c-linker-flags options)
        (list "-o" out-path)))
  
  (when (build-options-show-flags? options)
    (displayln (format "CXX link flags: ~a" link-flags)))

  (apply run-cmd
         cxx-path
         (append link-flags obj-files)))


(define (link-and-build-bin project-path)
  (define local-bin (build-path project-path "out.bin"))
  (define global-bin "/tmp/ti/out.bin")

  (compile-objects-to-bin project-path (path->string local-bin))

  (when (file-exists? global-bin)
    (delete-file global-bin))
  
  (copy-file local-bin global-bin)
  
  (displayln (format "Build successful: ~a" global-bin)))


