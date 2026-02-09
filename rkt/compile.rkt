#lang racket


(require "load-module.rkt"
	 "compile-blessed.rkt"
	 "build.rkt"
	 "desugar.rkt"
	 "simplify.rkt")


(provide compile-one) 


;;;;;;;; Compiles one files/nm/file.ext0 to nm/file.ext1 ;;;;;;;;;


(define (compile-one folder-name)
  (define dir (build-path "/tmp/ti/files" folder-name))

  (define (compile-step src-ext dest-ext step-func)
    (define src-file 
      (for/first ([f (in-list (directory-list dir #:build? #t))] 
                  #:when (path-has-extension? f src-ext))
		 f))

    (define dest-file 
      (and src-file (path-replace-extension src-file dest-ext)))

    (when (and src-file dest-file
               (not (file-exists? dest-file)))
      (define result (step-func src-file))
      (with-output-to-file dest-file
        (lambda () (if (string? result)
		       (display result)
		       (pretty-write result)))
        #:exists 'replace)))
   
  (compile-step ".ti" ".core" desugar-pass)
  (compile-step ".core" ".bl" simplify-lower-pass)
  (compile-step ".bl" ".cpp" compile-bl-pass)
  (compile-step ".bl" ".h" compile-bl-decls-pass)
  
  (void))


;;;;;;;;;; Individual Passes ;;;;;;;;;;;;


(define (desugar-pass src-path)
  (define mod (load-module src-path))
  (match mod
    [`(module ,name ,bless ,solo-inline ,blessed ,lets ,defs)
     (define all-inline (read-all-inline))
     (desugar-module ;; Desugar the module to core forms
      `(module ,name ,bless ,all-inline ;; <-- drop in all
	       ,blessed ,lets ,defs))]))


(define (simplify-lower-pass src-path)
  (define mod (with-input-from-file src-path read))
  (simplify-module mod))


(define (compile-bl-decls-pass src-path)
  (define mod (with-input-from-file src-path read))
  (compile-blessed-decls mod))


(define (compile-bl-pass src-path)
  (define mod (with-input-from-file src-path read))
  (define comp-bless (compile-blessed mod))
  comp-bless)







