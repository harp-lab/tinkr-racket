#lang racket

(require "inlining-helpers.rkt"
         "../helpers.rkt")

(provide inlining-pass)

;; Based on "Fast and Effective Procedure Inlining" (https://dl.acm.org/doi/10.5555/647166.717859)

(define (inlining-pass mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)

     (define defs+ (optimize/defs defs))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs+ ,methods ,types)]))

;; (ListOf Expr) -> (ListOf Expr)
(define (optimize/defs defs)
  (for/list ([def defs])
    (optimize/def def)))

;; Expr -> Expr
(define (optimize/def def-ast)
  (match def-ast
    [`(def (,xs ...) ,anns ... ,body)
      (define new-body
        (strip-ast-annotations 
          (optimize/ast
            (insert-ast-annotations body)
            'value
            (environment (hash) #f #f #f #f))))
      
      `(def (,@xs) ,@anns ,new-body)]
    [_ (error 'optimize/def "Unexpected AST: ~a" def-ast)]))

;; Expr Environment -> Expr
(define (optimize/ast ast context env)
  (match ast
    [`(const ,c)
      (inc-size-total! env)
      
      (cond
        [(effect-context? context) '(const void)]

        ;; All values except (const false) are truthy. ;; TODO: is this correct?
        [(and (test-context? context) (not (equal? c '(const false))))
          '(const true)]

        ;; We need the value of the constant still
        [else `(const ,c)])]

    ;; TODO: do more with this
    [`(bless ,e0)
     (inc-size-total! env)
     `(bless ,e0)]

    ;; Evalutate e1 for its effect, then evaluate e2 for the current context
    [`(seq ,e1 ,e2)
      (define e1^ (optimize/ast e1 'effect env))
      (define e2^ (optimize/ast e2 context env))

      (inc-size-total! env) ;; Note: overly-conservative size estimate since make-seq may discard e1.

      (make-seq e1^ e2^)]

    [`(if ,g ,e1 ,e2)
      (inc-size-total! env)

      (define g^ (optimize/ast g 'test env))
      (define g-res (result g^))

      ;; We don't want to propogate an application context down the if branches
      (define e-context (replace-app-context context 'value))

      (cond
        ;; Always go down the true branch
        [(equal? g-res '(const true))
         (define e1^ (optimize/ast e1 e-context env))
         (make-seq g^ e1^)]

        ;; Always go down the false branch
        [(equal? g-res '(const false))
         (define e2^ (optimize/ast e2 e-context env))
         (make-seq g^ e2^)]
        
        ;; Could be either branch
        [else
          (define e1^ (optimize/ast e1 e-context env))
          (define e2^ (optimize/ast e2 e-context env))

          (match* (e1^ e2^)
            ;; Both branches evaluate to the same constant, so just return the constant,
            ;; letting the guard expression be evaluated for just its effect.
            [(`(const ,c1) `(const ,c2)) #:when (equal? c1 c2)
              (make-seq g^ e1^)]
            
            ;; Otherwise, just return the if
            [(_ _)
              `(if ,g^ ,e1^ ,e2^)])])]

    [`(continue-dispatch ,es ...)
     (inc-size-total! env)
     `(continue-dispatch ,@es)]
    
    ;; TODO:
    [`(fail)
     (inc-size-total! env)
     `(fail)]

    ;; TODO:
    [`(,ell ,e0) #:when (eq? ell '|...|)
     (inc-size-total! env)
     `(,ell ,(optimize/ast e0 'value env))]
    
    ;; TODO:
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (inc-size-total! env)
      `(,ctor ,@(map (lambda (e) (optimize/ast e 'value env)) es))]

    [`(let (ref ,x) ,rhs ,body)
     (define op (construct-operand rhs env))
     (define x^ (copy-variable x))
     (define x^-with-op (variable-set-op x^ op))

     ;; Optimize the body with x mapped to x^
     ;; We need to use try-optimize since propogating may increase size or effort too much.
     (define body^
      (try-optimize env
        (lambda (env^)
          (define eb-env-with-op (extend-env env^ (list x) (list x^-with-op)))
          (optimize/ast body (replace-app-context context 'value) eb-env-with-op))
        (lambda () ;; On abort:
          (define eb-env (extend-env env (list x) (list x^))) ;; Optimize without the operands bound
          (optimize/ast body (replace-app-context context 'value) eb-env))))
     
     (match-define (var x-sym _ flags source-flags) x^)
     (define x-is-ref (set-member? flags 'ref))

     (define op-e
      (cond
        ;; The operand is no longer needed as a value
        [(not x-is-ref)
          (visit-op op 'effect)]
        
        [else
          (visit-op op 'value)]))

     (inc-size-total! env)
     (accumulate-size-total! env (get-env-size-total (unbox (opnd-env op))))

     ;; We can remove the let binding if x is not referenced in the body
     (if (not x-is-ref)
         (make-seq op-e body^)
         `(let (ref ,x^) ,op-e ,body^))]

    ;; TODO:
    [`(|[]| ,es ...)
     (inc-size-total! env)
     `(|[]| ,@(map (lambda (e) (optimize/ast e 'value env)) es))]

    ;; Inner def
    [`(def ((ref ,fx) ,params ...) ,anns ... ,body ,more)
     ;; TODO: handle siblings

     (define fn-val `(fn (,@params) (,@anns) ,body))
     (define fx-op (construct-operand fn-val env))
     (define fx^ (copy-variable fx))
     (define fx^-with-op (variable-set-op fx^ fx-op))

     ;; Optimize `more` with `fx` mapped to `fx^`
     ;; We need to use try-optimize since propogating may increase size or effort too much.
     (define more^
      (try-optimize env
        (lambda (env^)
          (define more-env-with-op (extend-env env^ (list fx) (list fx^-with-op)))
          (optimize/ast more (replace-app-context context 'value) more-env-with-op))
        (lambda () ;; On abort:
          (define more-env (extend-env env (list fx) (list fx^))) ;; Optimize without the operand bound
          (optimize/ast more (replace-app-context context 'value) more-env))))
     
     (match-define (var fx-sym _ flags source-flags) fx^)
     (define fx-is-ref (set-member? flags 'ref))

     (if (not fx-is-ref)
         ;; The def is no longer needed
         more^

         ;; Otherwise, visit the def for value
         (let ([op-e (visit-op fx-op 'value)])
          (inc-size-total! env)
          (accumulate-size-total! env (get-env-size-total (unbox (opnd-env fx-op))))

          (match-define `(fn (,params^ ...) ,_ ,body^) op-e)

          `(def ((ref ,fx) ,@params^) ,@anns ,body^ ,more^)))]

    [`(fn ((ref ,params) ...) ,anns ,body)
      (match context
        ['test (inc-size-total! env) '(const true)]
        ['effect (inc-size-total! env) '(const void)]

        ;; Just leave the fn alone (and recur down the body)
        ['value
          ;; Create new variables for the parameters.
          (define params^ (copy-variables params))
          (define body-env (extend-env env params params^))

          (define body^ (optimize/ast body 'value body-env))

          (inc-size-total! env)

          `(fn (,@(map add-ref params^)) ,anns ,body^)]

        ;; Function is in an application context, so try to apply it.
        [(app-context ops c inlined?)
          (define app-result (apply-expr ast context env))

          (if app-result
              app-result
              (optimize/ast ast 'value env))])]

    [`(ref ,x)
      (match-define (var x-sym x-op x-flags x-source-flags) x)

      (cond
        [(not (env-has? env x))
          ;; TODO: this case should not be needed
          (set-add! x-flags 'ref)
          `(ref ,x)]
        [else
          (define x^ (env-ref env x))
          (match-define (var x^-sym op x^-flags x^-source-flags) x^)

          (cond
            ;; If in an effect context, then we don't care about the reference
            [(equal? context 'effect)
              (inc-size-total! env)
              '(const void)]

            ;; If x^ is not bound to an operand then we can't inline/propogate it.
            [(null? op)
              ;; Mark it as a ref if it wasn't already.
              (set-add! x^-flags 'ref)

              (inc-size-total! env)

              `(ref ,x^)]

            ;; Otherwise, we can try to copy/propogate the value of x^ into the reference site.
            [else
              ;; Get the operand expression and then try to copy it to the reference site.
              (define op-e (visit-op op 'value))

              (define op-size (get-env-size-total (unbox (opnd-env op))))

              ;; Note: this is overly conservative. We should be able to copy
              ;;   things like constants and immutable references for free.
              ;;   Also, for lambdas, if they get folded after propogation, then
              ;;   we should take the resulting size into account.
              (if (set-member? x^-flags 'copied)
                  (accumulate-size-delta! env op-size)
                  
                  ;; Hasn't been copied before, so mark it as copied and there is no need to accumulate
                  ;; the size delta for the first copy.
                  (set-add! x^-flags 'copied))

              (copy x^ (result op-e) context env)])])]

    [(or `(extern-ref ,x) `(fallback-ref ,x))
     (inc-size-total! env)
     (cond
        [(test-context? context) '(const true)]
        [(effect-context? context) '(const void)]
        [else ast])]

    ;; Untagged application
    [`(,ef ,es ...)
     ;; Create an application context for ef so that the processing of ef can
     ;; perform inlining if possible.
     (define ops (construct-operands es env))
     (define ef-context (app-context ops context (box #f)))

     (define ef^ (optimize/ast ef ef-context env))
     (define inlined? (unbox (app-context-inlined? ef-context)))

     (cond
      ;; Ignore the operands and just return the inlined result
      [inlined? ef^]

      ;; ef has not been inlined, so process the operands and then return the call expression
      [else
        (define op-es (map (lambda (op) (visit-op op 'value)) ops))

        (inc-size-total! env)
        (for ([op ops])
          (accumulate-size-total! env (get-env-size-total (unbox (opnd-env op)))))

        `(,ef^ ,@op-es)])]))

;; Opnd Context -> Expr
;; Residualize an operand/argument expression (if it has already been visited,
;; it will use the cached version)
(define (visit-op op context)
  (match-define (opnd e (box env) cache) op)
  (define c (unbox cache))

  (cond
    ;; We have already processed the operand, so just use the cached version.
    [c c]

    ;; We need to process the operand expression for the first time (cache is #f).
    [else
      (define e^ (optimize/ast e context env))
      (set-box! cache e^)
      e^]))

;; Var Expr Context Environment -> Expr
;; Handles copy propogation and inlining at a variable reference site.
;; x is the variable reference site. e is the expression that x refers to.
(define (copy x e context env)
  (match-define (var x-sym op flags source-flags) x)

  (define e-tag (car e))

  (cond
    ;; Propogate constants
    [(equal? e-tag 'const)
      (match-define `(const ,c) e)
      (optimize/ast `(const ,c) context env)]

    ;; Propogate variable references
    [(or (equal? e-tag 'ref) (equal? e-tag 'fallback-ref))
      e]

    ;; Inline functions into application contexts and try to apply reduce them
    [(and (app-context? context) (equal? e-tag 'fn))
      (define app-result (apply-expr e context env))
      (if app-result
          app-result

          (begin
            (set-add! flags 'ref)
            `(ref ,x)))]

    ;; Truthy values in a test context can be replaced with (const true)
    [(and (test-context? context)
          (truthy? e))
      '(const true)]

    ;; Can allways propogate an extern-ref.
    [(equal? e-tag 'extern-ref)
      e]

    ;; Otherwise, just leave the reference alone (mark it as a reference if needed).
    [else
      (set-add! flags 'ref)
      `(ref ,x)]))

;; `(fn ...) Context Environment -> (or Expr #f)
;; Tries to apply a function.
(define (apply-expr expr context env)
  (match expr
    [`(fn (,params ...) ,anns ,body)
      (try-optimize env
        (lambda (env^)
          (apply-fn expr context env^))
        (lambda () ;; On abort:
          #f))]))

(define (apply-fn expr context env)
  ;; TODO
  (abort-inlining-attempt env))

;; Helper to sequence expressions (ensuring that the
;; last expression in the sequence is not a sequence itself).
(define (make-seq e1 . es)
  (define (make-seq-pair e1 e2)
    (match* (e1 e2)
      [((? no-effect? e1) _) e2]
      [(_ `(seq ,e3 ,e4)) `(seq (seq ,e1 ,e3) ,e4)]
      [(_ _) `(seq ,e1 ,e2)]))

  ;; Note: for more than two expression, void constants may not be removed here.
  (if (null? es)
      e1 ;; No need for a seq

      (let ([e2 (first es)]
            [es (rest es)])
        (if (null? es)
          ;; Only two expressions, so just make a seq pair
          (make-seq-pair e1 e2)

          ;; More than two expressions, so make a seq pair for the first two and then recur
          (apply make-seq (make-seq-pair e1 e2) es)))))

;; Helper to ignore sequence expressions and just return the last expression in the sequence.
(define (result e)
  (match e
    [`(seq ,_ ,e2) e2]
    [else e]))

;; TODO
(define (no-effect? expr)
  (match expr
    [`(const ,_) #t]
    [`(extern-ref ,_) #t]
    [`(fallback-ref ,_) #t]
    [`(ref ,x) #t]
    [_ #f]))

;; TODO
(define (truthy? expr)
  (match expr
    [`(const false) #f]
    [`(const ,_) #t]
    [`(extern-ref ,_) #t]
    [`(fallback-ref ,_) #t]
    [_ (displayln 'TODO-extend-truthy?) #f]))

;; Expr [HashOf Var Var] -> Expr
;; Add extra data to the AST for optimization purposes (e.g. variable locations, flags, etc.).
(define (insert-ast-annotations ast [env (hash)])
  (define (recur ast)
    (insert-ast-annotations ast env))
  
  (match ast
    [`(const ,c) `(const ,c)]

    [`(bless ,e0) `(bless ,e0)]

    [`(if ,g ,t ,e)
     `(if ,(recur g) ,(recur t) ,(recur e))]

    [`(continue-dispatch ,es ...)
     `(continue-dispatch ,@(map recur es))]
    
    [`(fail) `(fail)]

    [`(,ell ,e0) #:when (eq? ell '|...|)
     `(,ell ,(recur e0))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      `(,ctor ,@(map recur es))]

    [`(let (ref ,x) ,rhs ,body)
      (define new-x (new-variable x))
      (define env-body (hash-set env x new-x))

      `(let (ref ,new-x) ,(recur rhs) ,(insert-ast-annotations body env-body))]

    [`(|[]| ,es ...)
     `(|[]| ,@(map recur es))]

    ;; Inner def
    [`(def ((ref ,fx) ,params ...) ,anns ... ,body ,more)
     (define fx-var (new-variable fx))
     (define more-env (hash-set env fx fx-var))

     (define-values (body-env new-params)
        (for/foldr ([body-env more-env]
                    [new-params (list)])
                   ([param params])
          
          (define new-param (apply-to-ref-sym param new-variable))
          (values (hash-set body-env param new-param)
                  (cons new-param new-params))))

     `(def ((ref ,fx-var) ,@new-params) ,@anns
           ,(insert-ast-annotations body body-env)
           ,(insert-ast-annotations more more-env))]

    ;; TODO: we may want to handle true and false differently in the rest of the compiler (since
    ;; treating them as refs means they can be shadowed by user code).
    [`(ref true) `(const true)]
    [`(ref false) `(const false)]

    [`(ref ,x)
     (define new-x (hash-ref env x #f))
     (if new-x
         `(ref ,new-x)
         `(extern-ref ,x))]

    [`(fallback-ref ,x)
     `(fallback-ref ,x)]

    ;; Untagged application
    [`(,fe ,es ...)
     `(,(recur fe) ,@(map recur es))]))

;; Expr -> Expr
(define (strip-ast-annotations ast)
  (define (recur ast)
    (strip-ast-annotations ast))

  (match ast
    [`(const true) `(ref true)]
    [`(const false) `(ref false)]
    [`(const void) `(const 0)]

    [`(const ,c) `(const ,c)]

    [`(bless ,e0) `(bless ,e0)]
    
    [`(seq ,e1 ,e2)
      (define seq-x (gensym 'seq))
      `(let (ref ,seq-x) ,(recur e1)
            ,(recur e2))]

    [`(if ,g ,t ,e)
     `(if ,(recur g) ,(recur t) ,(recur e))]

    [`(continue-dispatch ,es ...)
     `(continue-dispatch ,@(map recur es))]
    
    [`(fail) `(fail)]

    [`(,ell ,e0) #:when (eq? ell '|...|)
     `(,ell ,(recur e0))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      `(,ctor ,@(map recur es))]

    [`(let (ref ,x) ,rhs ,body)
     `(let (ref ,(var-name x)) ,(recur rhs) ,(recur body))]

    [`(|[]| ,es ...)
     `(|[]| ,@(map recur es))]

    ;; Inner def
    [`(def ((ref ,fx) ,params ...) ,anns ... ,body ,more)
     (define new-params
      (map
        (lambda (p)
          (apply-to-ref-sym p var-name))
        params))
      
     `(def ((ref ,(var-name fx)) ,@new-params) ,@anns ,(recur body) ,(recur more))]

    [`(ref ,x)
     `(ref ,(var-name x))]

    [`(fallback-ref ,x)
     `(fallback-ref ,x)]

    [`(extern-ref ,x)
     `(ref ,x)]

    ;; Untagged application
    [`(,fe ,es ...)
     `(,(recur fe) ,@(map recur es))]))