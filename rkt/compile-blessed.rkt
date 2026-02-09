#lang racket


(provide compile-blessed-decls
	 compile-blessed
	 compile-bless)


(require "utils.rkt")


(define (compile-bless-expr ast)
  (match ast
    [`(ref ,x) (~a x)]
    
    [`(const ,(? integer? z)) (~a z)]
    [`(const ,(? string? s)) (~a s)]
    
    [`((const ,(? string? fmt-str)) ,args ...)
     ;; arg is either `(ref ,x) or `(const ,c)
     (bless-format fmt-str (map compile-bless-expr args))]

    [_ (error (format "Unrecognized bless-ir expr code: ~a" ast))]))


(define (compile-bless-ast ast) 
  (define (compile-bless-arg arg)
    (format "(any)~a" (compile-bless-expr arg)))
  (match ast
    ;; Basic Block
    [`((ref |{}|)) "{(void)0;}\n"]
    [`((ref |{}|) ,es ...)
     (format "{\n~a}\n" (indent-string (string-join (map compile-bless-ast es) "")))]

    ;; Do Stmt
    [`(do ,rhs) (format "~a;\n" (compile-bless-expr rhs))]

    ;; Conditional Stmt
    [`(if ,ge ,te ,fe)
     (format "if ((u64)~a)\n~aelse\n~a"
	     (compile-bless-arg ge)
	     (compile-bless-ast te) (compile-bless-ast fe))]

    ;; Temp Assign Stmt
    [`(temp (ref ,x) ,rhs)
     (format "any ~a = ~a;\n" x (compile-bless-arg rhs))]

    ;; Set Assign Stmt
    [`(set ((ref |!|) (ref ,x)) ,rhs)
     (format "~a = (many)~a;\n" x (compile-bless-expr rhs))]

    ;; Call Assign Stmt
    [`(assigncall (ref ,x) ((ref ,fname) ,args ...))
     (string-append
      (format "r = ~a(alloc_fr,alloc_bk,stack_fr~a);\n"
	      (format "((blessed_t)~a)" fname)
	      (let ([args (string-join (map compile-bless-arg args) ",")])
		(if (equal? args "") "" (string-append "," args))))
      "alloc_fr = r.m0();\nalloc_bk = r.m1();\nstack_fr = r.m2();\n"
      (format "any ~a = r.a0();\n" x))]

    ;; Tail Call Assign Stmt
    [`(tailcall ((ref ,fname) ,args ...))
     (format "tailcall ~a(alloc_fr,alloc_bk,stack_fr~a);\n"
	     (format "((blessed_t)~a)" fname)
	     (let ([args (string-join (map compile-bless-arg args) ",")])
	       (if (equal? args "") "" (string-append "," args))))]
    
    ;; Return Stmt
    [`(return ,e0)
     (format "return AVXRet::a1m3(~a,alloc_fr,alloc_bk,stack_fr);\n"
	     (compile-bless-arg e0))]

    [_ (error (format "Unknown bless stmt ~a" ast))]))


(define (collect-mut ast)
  (match ast
    [`((ref |!|) (ref ,x)) (set x)]
    [`(,es ...) (foldl set-union (set) (map collect-mut es))]
    [_ (set)]))


(define (format-args args)
  (string-join (map (lambda (a)
		      (match a
			[`(ref ,arg) (format "any ~a" arg)]
			[`((ref |!|) (ref ,arg)) (format "many ~a" arg)]))
		    args)
	       ", "))


(define (format-body body)
  (match body
    [`((ref |{}|) ,es ...)
     (indent-string (string-join (map compile-bless-ast es) ""))]
    [_ (compile-bless-ast body)]))
  

(define (compile-blessed-decl ast) 
  (match ast
    
    [`(blessed ((ref ,name)) ,body)
     (format "reg_passing AVXRet ~a(many alloc_fr, many alloc_bk, many stack_fr);\n" name)]

    [`(blessed ((ref ,name) ,args ...) ,body)
     (format "reg_passing AVXRet ~a(many alloc_fr, many alloc_bk, many stack_fr, ~a);\n" name (format-args args))]))


(define (compile-blessed-ast ast) 
  (match ast
    
    [`(blessed ((ref ,name)) ,body)
     (format "reg_passing AVXRet ~a(many alloc_fr, many alloc_bk, many stack_fr)\n{\n  AVXRet r;\n~a~a~a}\n\n"
	     name
	     (format "DBG(\"Entering blessed_t ~a\");\n" name)
	     (let ([vrs (string-join (map ~a (set->list (collect-mut body))) ", ")])
	       (if (equal? vrs "")
		   "  many tmp;\n"
		   (format "  many tmp,~a;\n" vrs)))
	     (format-body body))]

    [`(blessed ((ref ,name) ,args ...) ,body)
     (format "reg_passing AVXRet ~a(many alloc_fr, many alloc_bk, many stack_fr, ~a)\n{\n  AVXRet r;\n~a~a~a}\n\n"
	     name
	     (format-args args)
	     (format "DBG(\"Entering blessed_t ~a\");\n" name) 
	     (let ([vrs (string-join (map ~a (set->list (collect-mut body))) ", ")])
	       (if (equal? vrs "")
		   "  many tmp;\n"
		   (format "  many tmp,~a;\n" vrs)))
	     (format-body body))]))


(define ((simplify-blessed-expr inline-h) ast env) 
  (define (recur ast) ((simplify-blessed-expr inline-h) ast env))
  (match ast
    ;; References may be replaced via env
    [`(ref ,(? symbol? x)) (hash-ref env x (lambda () ast))]

    ;; Leave constants alone
    [`(const ,c) ast]

    ;; Freeze banged variables
    [`((ref |!|) (ref ,x))
     (recur `((ref freeze) (ref ,x)))]

    ;; Leave format expressions alone and continue under
    [`((const ,(? string? s)) ,args ...)
     `((const ,s) ,@(map recur args))]

    ;; Handle inline expression calls
    [`((ref ,fx) ,args ...)
     #:when (hash-has-key? inline-h fx)
     (match (hash-ref inline-h fx)
       [`(blessed ((ref ,_) ,params ...) ,body)
	#:when (= (length params) (length args))
	((simplify-blessed-expr inline-h)
	 body
	 (foldl (lambda (p a env)
		  (match p [`(ref ,px) (hash-set env px a)]))
		env
		params
		(map recur args)))]
       [_ (error "Inline Function ~a does not match call ~a"
		 (hash-ref inline-h fx) ast)])]

    [_ (error (format "simplify-blessed-expr: unknown expression ~a" ast))]))


(define ((simplify-blessed-ast inline-h) ast [env (hash)]) 
  (define (recur ast) ((simplify-blessed-ast inline-h) ast env))
  (define (t-expr ast) ((simplify-blessed-expr inline-h) ast env))
  (define mut-vars (collect-mut ast))
  (define (optimize-block es)
    (match es ;; todo: optimize sequenced allocations here...
      [`(((ref =) (ref ,x) ,rhs) (return (ref ,x)) ,_ ...)
       `((return ,rhs))]
      [`((return (ref ,x)) ,_ ...)
       #:when (set-member? mut-vars x)
       `(((ref =) (ref tmp_froz) ((ref |!|) (ref ,x)))
	 (return (ref tmp_froz)))]
      [`(,e0 ,es+ ...) `(,e0 ,@(optimize-block es+))]
      ['() '()]))
  (match ast
    [`(do ((ref ,fx) ,args ...))
     #:when (hash-has-key? inline-h fx)
     `(do ,(t-expr `((ref ,fx) ,@args)))]
    [`(do ((ref ,fx) ,args ...))
     (recur `((ref =) (ref ,(gensymb '_)) ((ref ,fx) ,@args)))]
    [`(do ,e0) `(do ,(t-expr e0))]

    ;; Rewrite allocation in terms of clang.ti prims
    [`((ref =) ((ref |!|) (ref ,x)) ((ref alloc) ,(? integer? n)))
     #:when (> n 40)
     `(set ((ref |!|) (ref ,x)) ,(t-expr `((ref alloc_gc) (const ,n))))]
    
    [`((ref =) ((ref |!|) (ref ,x)) ((ref alloc) ,n-exp))
     (recur
      `((ref |{}|)
	(do ((ref alloc_attempt) (ref ,x) ,n-exp))
	(if ((ref alloc_is_valid))
	    ((ref |{}|)) ;; if valid, do nothing; otherwise:
	    (if ((ref lte) ,n-exp (const 40))
		((ref |{}|) ;; if short, refresh, alloc again
		 (do ((ref alloc_refresh)))
		 (do ((ref alloc_attempt) (ref ,x) ,n-exp)))
		((ref |{}|) ;; if long, rollback, use alloc_gc
		 (do ((ref alloc_rollback) ,n-exp))
		 ((ref =) ((ref |!|) (ref ,x))
		  ((ref alloc_gc) ,n-exp)))))))]

    [`((ref =) ((ref |!|) (ref ,x)) ,rhs)
     `(set ((ref |!|) (ref ,x)) ,(t-expr rhs))]
    
    [`((ref =) (ref ,x) ((ref ,fname) ,args ...))
     #:when (hash-has-key? inline-h fname)
     `(temp (ref ,x) ,(t-expr `((ref ,fname) ,@args)))]

    [`((ref =) (ref ,x) ((ref ,fx) ,args ...))
     #:when (not (eq? fx '|!|))
     `(assigncall (ref ,x)
		  ((ref ,fx) ,@(map t-expr args) ,@(pad-args (length args))))]

    [`((ref =) (ref ,x) ,rhs)
     `(temp (ref ,x) ,(t-expr rhs))]
    
    [`((ref |{}|) ,args ...)
     `((ref |{}|) ,@(map recur (optimize-block args)))]

    [`(if ,ge ,(and te `((ref |{}|) . ,_)) ,(and fe `((ref |{}|) . ,_)))
     `(if ,(t-expr ge) ,(recur te) ,(recur fe))]
    [`(if ,ge ,te ,(and fe `((ref |{}|) . ,_)))
     `(if ,(t-expr ge) ((ref |{}|) ,(recur te)) ,(recur fe))]
    [`(if ,ge ,(and te `((ref |{}|) . ,_)) ,fe)
     `(if ,(t-expr ge) ,(recur te) ((ref |{}|) ,(recur fe)))]
    [`(if ,ge ,te ,fe)
     `(if ,(t-expr ge) ((ref |{}|) ,(recur te)) ((ref |{}|) ,(recur fe)))]

    [`(return ((ref ,fname) ,args ...))
     #:when (not (hash-has-key? inline-h fname))
     `(tailcall ((ref ,fname) ,@(map t-expr args) ,@(pad-args (length args))))]
    
    [`(return ,e0)
     `(return ,(t-expr e0))]

    [`(blessed ((ref ,fx) ,params ...) ,body)
     `(blessed ((ref ,fx) ,@params ,@(pad-params (length params)))
	       ,(recur body))]

    [_ (error (format "simplify-blessed-ast: unknown exp ~a" ast))]))



(define (lst->set->hash lst)
  (for/hash ([(ast) (in-list lst)])
	    (match ast
	      [`(blessed ((ref ,fx) ,args ...) ,body)
	       (values fx ast)])))


(define (compile-bless inline bexp)
  (match bexp
    [`(bless ((const ,(? string? s)))) s]
    [`(bless ,e0) 
     (define inline-h (lst->set->hash inline))
     (compile-bless-expr
      ((simplify-blessed-expr inline-h) e0 (hash)))]))


(define (compile-blessed-decls mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define inline-h (lst->set->hash inline))
     (define proc-h+
       (for/hash ([(nm ast) (in-hash (lst->set->hash blessed))])
		 (values nm ((simplify-blessed-ast inline-h) ast))))
     (foldr string-append
	    (foldr string-append ""
		   (for/list ([(ast) (in-list lets)])
			     (match ast [`(let (ref ,x) ,_)
					 (format "extern const void* ~a;\n" x)])))
	    (for/list ([(ast) (in-hash-values proc-h+)])
		      (compile-blessed-decl ast)))]))


(define (compile-blessed mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define inline-h (lst->set->hash inline))
     (define proc-h+
       (for/hash ([(nm ast) (in-hash (lst->set->hash blessed))])
		 ;;(pretty-print ast) (newline)
		 (values nm ((simplify-blessed-ast inline-h) ast))))
     (define def-let-bless
       (foldr string-append ""
	      (for/list ([(ast) (in-hash-values proc-h+)])
			(compile-blessed-ast ast))))
     (define all-bless (foldr (lambda (b acc)
				(string-append (compile-bless inline b) "\n" acc))
			      def-let-bless
			      bless))
     (string-append
      (foldr string-append ""
		     (for/list ([(ast) (in-list lets)])
			       (match ast [`(let (ref ,x) ,_)
					   (format "const void* ~a = 0;\n" x)])))
      all-bless)]))



