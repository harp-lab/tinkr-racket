#lang racket

;; Used to recompile existing generated C++.
;; Usage:
;;  racket debug/comp-cpp.rkt <project-name>
;; <project-name> is in the form: <name>_ti_<hash>

(require "../rkt/build.rkt"
         "../rkt/build-process.rkt"
         racket/system
         racket/hash
         file/sha1
         racket/runtime-path
         racket/list)


(module+ main
  (require racket/cmdline)

  (define debug-mode (make-parameter #f))
  (define no-lto (make-parameter #f))
  (define no-opt (make-parameter #f))
  (define no-strict-aliasing (make-parameter #f))
  (define show-flags (make-parameter #f))
  (define print-cmds (make-parameter #f))
  (define project
    (command-line #:program "comp-cpp.rkt"
                  #:once-each [("-d" "--debug") "Run in debug mode" (debug-mode #t)]
                  #:once-each [("--no-lto") "Don't pass lto flags to C++ compiler." (no-lto #t)]
                  #:once-each [("--no-opt") "Don't pass -O2 flag to C++ compiler." (no-opt #t)]
                  #:once-each [("--no-strict-aliasing") "Pass strict aliasing flag to C++ compiler." (no-strict-aliasing #t)]
                  #:once-each [("--show-flags") "Print flags passed to the C++ compiler." (show-flags #t)]
                  #:once-each [("--print-cmds") "Print the commands that the compiler runs" (print-cmds #t)]
                  #:args (filename)
                  filename))

  (when (not project)
    (error "No project name specified."))
  
  (define options (build-options (debug-mode) #f (not (no-lto)) (not (no-opt)) (no-strict-aliasing) (show-flags) (print-cmds)))
  (set-options! options)

  (current-directory "/tmp/ti/build")

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
