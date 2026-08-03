#lang racket

(require "../rkt/build.rkt")

(module+ main
  (require racket/cmdline)

  (define debug-mode (make-parameter #f))
  (define separate-logs (make-parameter #f))
  (define no-lto (make-parameter #f))
  (define no-opt (make-parameter #f))
  (define no-strict-aliasing (make-parameter #f))
  (define show-flags (make-parameter #f))
  (define print-cmds (make-parameter #f))
  (define clean-mode (make-parameter #f))
  (define test-file
    (command-line #:program "test.rkt"
                  #:once-each [("-d" "--debug") "Run in debug mode" (debug-mode #t)]
                  #:once-each [("-s" "--separate-logs") "Separate log files by thread" (separate-logs #t)]
                  #:once-each [("--no-lto") "Don't pass lto flags to C++ compiler." (no-lto #t)]
                  #:once-each [("--no-opt") "Don't pass -O2 flag to C++ compiler." (no-opt #t)]
                  #:once-each [("--no-strict-aliasing") "Pass strict aliasing flag to C++ compiler." (no-strict-aliasing #t)]
                  #:once-each [("--show-flags") "Print flags passed to the C++ compiler." (show-flags #t)]
                  #:once-each [("--print-cmds") "Print the commands that the compiler runs" (print-cmds #t)]
                  #:once-each [("-c" "--clean") "Wipe the /tmp/ti cache before building" (clean-mode #t)]
                  #:args (filename)
                  filename))

  (when (clean-mode) (void (system "rm -rf /tmp/ti")))

  (if test-file
    (build-project test-file (build-options (debug-mode) (separate-logs) (not (no-lto)) (not (no-opt)) (no-strict-aliasing) (show-flags) (print-cmds) '() '()))
    (error "No test file specified.")))
