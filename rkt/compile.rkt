#lang racket


(require "load-module.rkt"
	 "compile-blessed.rkt"
	 "build.rkt"
	 "desugar.rkt"
	 "simplify.rkt"
	 "utils.rkt"
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
      ;; Publish atomically (write + rename): a build killed mid-write must
      ;; never leave a partial artifact that a later cached build would trust.
      (define tmp-file (string->path (string-append (path->string dest-file) ".tmp")))
      (with-output-to-file tmp-file
        (lambda () (if (string? result)
		       (display result)
		       (pretty-write result)))
        #:exists 'replace)
      (rename-file-or-directory tmp-file dest-file #t)))
   
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
  (define mod+ (alphatize-mod mod))
  ;; Record this module's free (global) names for the linker/qualifier.
  ;; These are the C-escaped spellings of every top-level name the module
  ;; references but does not bind locally.
  (with-output-to-file (path-replace-extension src-path ".globals")
    #:exists 'replace
    (lambda () (write (set->list global-names))))
  ;; Names whose absence must be a runtime dispatch error (closure
  ;; fallbacks), not a shim to an assumed C function.
  (with-output-to-file (path-replace-extension src-path ".soft")
    #:exists 'replace
    (lambda () (write (set->list soft-globals))))
  mod+)


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


;; Names that must keep their global spelling:
;; - v_equal is the inline fast-path for =, which itself dispatches to the
;;   global _u_0003d ( = ) dispatcher (wired into header.h).
;; - _u__subword/_u__slice/_u__fun__ptr are the shared special type tags
;;   (C-escaped _subword/_slice/_fun_ptr); desugar references them without
;;   registering them in every module's type list.
(define never-qualify
  (set 'v_equal '_u_0003d '_u__subword '_u__slice '_u__fun__ptr))

;; Rewrites every reference to a free (global) name x into the
;; module-qualified spelling mv_<module-dir>__x. Which symbol that names is
;; the linker's decision: a per-module view dispatcher, a shim to a blessed
;; C function, or an alias to a top-level let.
(define (qualify-mod mod globals)
  (define used (mutable-set)) ;; free names that actually occur in the code
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     ;; Type tags are values (vtable pointers / subword indices) emitted by
     ;; the linker under their global names; they must not be qualified.
     (define type-names (for/set ([t (in-list types)]) (escape-id-for-C t)))
     ;; The module's own compiled functions (fail_to chain hops, konts, its
     ;; hand-written blessed) are called directly by name; leave them alone.
     (define own-fn-names
       (for/set ([b (in-list blessed)])
         (match b [`(blessed ((ref ,fx) ,_ ...) ,_) fx])))
     (define qset (set-subtract globals never-qualify type-names own-fn-names))
     (define prefix (format "mv_~a__" name))
     (define (Q ast)
       (match ast
         [`(ref ,x) (if (set-member? qset x)
                        (begin
                          (set-add! used x)
                          `(ref ,(string->symbol (format "~a~a" prefix x))))
                        ast)]
         [`(const ,_) ast]
         [(? list? l) (map Q l)]
         [_ ast]))
     (define blessed+
       (for/list ([b blessed])
         (match b
           [`(blessed ,sig ,body) `(blessed ,sig ,(Q body))])))
     (values
      `(module ,name ,mtag ,bless ,inline ,blessed+ ,lets ,defs ,methods ,types)
      (sort (set->list used) symbol<?))]))

(define (read-globals src-path)
  (define p (path-replace-extension src-path ".globals"))
  (if (file-exists? p)
      (list->set (with-input-from-file p read))
      (set)))


(define (compile-bl-pass src-path)
  (define mod (with-input-from-file src-path read))
  (define-values (mod+ used) (qualify-mod mod (read-globals src-path)))
  ;; Record which qualified names this module's code actually uses;
  ;; the linker emits one mv_<dir>__<name> symbol per entry.
  (with-output-to-file (path-replace-extension src-path ".used")
    #:exists 'replace
    (lambda () (write used)))
  (define comp-bless (compile-blessed mod+))
  comp-bless)
