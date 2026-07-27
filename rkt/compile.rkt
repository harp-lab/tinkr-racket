#lang racket


(require "load-module.rkt"
	 "compile-blessed.rkt"
	 "build.rkt"
	 "desugar.rkt"
	 "simplify.rkt"
   "closure-convert.rkt")


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
   
  (compile-step ".ti" ".ti_loaded" load-module-pass)
  (compile-step ".ti_loaded" ".core" desugar-pass)
  (compile-step ".core" ".core_alpha" alphatize-pass)
  (compile-step ".core_alpha" ".core_clo" clo-convert-pass)
  (compile-step ".core_clo" ".core_limited_params" limit-def-params-pass)
  (compile-step ".core_limited_params" ".core_anf" anf-convert-pass)
  (compile-step ".core_anf" ".core_cps" cps-convert-pass)
  (compile-step ".core_cps" ".bl" lower-pass)
  (compile-step ".bl" ".cpp" compile-bl-pass)
  (compile-step ".bl" ".h" compile-bl-decls-pass)
  
  (void))


;;;;;;;;;; Individual Passes ;;;;;;;;;;;;

(define (load-module-pass src-path)
  (load-module src-path))


(define (desugar-pass src-path)
  ;;(define mod (load-module src-path))
  (define mod (with-input-from-file src-path read))
  (match mod
    [`(module ,name ,bless ,solo-inline ,blessed ,lets ,defs)
     (define all-inline (read-all-inline))
     (desugar-module ;; Desugar the module to core forms
      `(module ,name ,bless ,all-inline ;; <-- drop in all
	       ,blessed ,lets ,defs))]))


(define (alphatize-pass src-path)
  (define mod (with-input-from-file src-path read))
  (alphatize-mod mod))


(define (clo-convert-pass src-path)
  (define mod (with-input-from-file src-path read))
  (clo-convert-mod mod))


(define (limit-def-params-pass src-path)
  (define mod (with-input-from-file src-path read))
  (limit-def-params-in-mod mod))


(define (anf-convert-pass src-path)
  (define mod (with-input-from-file src-path read))
  (anf-convert-mod mod))


(define (cps-convert-pass src-path)
  (define mod (with-input-from-file src-path read))
  (cps-convert-mod mod))


(define (lower-pass src-path)
  (define mod (with-input-from-file src-path read))
  (lower-mod mod))


(define (compile-bl-decls-pass src-path)
  (define mod (with-input-from-file src-path read))
  (compile-blessed-decls mod))


(define (compile-bl-pass src-path)
  (define mod (with-input-from-file src-path read))
  (define comp-bless (compile-blessed mod))
  comp-bless)
