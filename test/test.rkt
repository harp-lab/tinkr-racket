#lang racket

(require "../rkt/build.rkt")

(module+ main
  (require racket/cmdline)

  (define debug-mode (make-parameter #f))
  (define separate-logs (make-parameter #f))
  (define clean-mode (make-parameter #f))
  (define test-file
    (command-line #:program "test.rkt"
                  #:once-each [("-d" "--debug") "Run in debug mode" (debug-mode #t)]
                  #:once-each [("-s" "--separate-logs") "Separate log files by thread" (separate-logs #t)]
                  #:once-each [("-c" "--clean") "Wipe the /tmp/ti cache before building" (clean-mode #t)]
                  #:args (filename)
                  filename))

  (when (clean-mode) (void (system "rm -rf /tmp/ti")))

  (if test-file
    (build-project test-file (debug-mode) (separate-logs))
    (error "No test file specified.")))
