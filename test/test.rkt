#lang racket

(require "../rkt/build.rkt")

(module+ main
  (require racket/cmdline)

  (define debug-mode (make-parameter #f))
  (define test-file
    (command-line #:program "test.rkt"
                  #:once-each [("-d" "--debug") "Run in debug mode" (debug-mode #t)]
                  #:args (filename)
                  filename))

  (void (system "rm -rf /tmp/ti")) ;; optional

  (if test-file
    (build-project test-file (debug-mode))
    (error "No test file specified.")))
