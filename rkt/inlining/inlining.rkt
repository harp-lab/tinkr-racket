#lang racket

(require "inlining-helpers.rkt"
         "bless-primitives.rkt"
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
            (make-empty-env))))

      `(def (,@xs) ,@anns ,new-body)]
    [_ (error 'optimize/def "Unexpected AST: ~a" def-ast)]))

;; Expr Environment -> Expr
(define (optimize/ast ast context env)
  (define effort (get-env-effort env))
  (when effort
    (if (< effort (get-effort-bound))
        (inc-env-effort! env)
        (begin
          (displayln (format "ABORTING INLINING ATTEMPT: effort = ~a" effort))
          (abort-inlining-attempt env))))

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

    [`(bless ,e0)
     (cond
      [(effect-context? context) '(const void)]
      [(test-context? context)
        (define e0^ (optimize/ast e0 context (set-env-under-blessed env #t)))

        (match e0^
          ['(const false) '(const false)]
          [`(const ,c) '(const true)]
          [else `(bless ,e0^)])]
      [else
        `(bless ,(optimize/ast e0 context (set-env-under-blessed env #t)))])]

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

    ;; TODO:
    [`(continue-dispatch ,es ...)
     (inc-size-total! env)
     `(continue-dispatch ,@es)]
    
    ;; TODO:
    [`(fail (ref ,fx) ,es ...)
     (define opt-fail (optimize/ast `((ref ,fx) ,@es) 'value env))

     (inc-size-total! env)
     
     (match opt-fail
      [`((ref ,fx^) ,es^ ...) #:when (equal? (var-name fx) (var-name fx^))
       ;; TODO: Make sure to handle the case where this call to fx has different es than the original call to fx (which might be possible
       ;;   when inlining a recursive call?). This should be handled when deciding whether to residualize a (fail) or regular application.
       `(fail (ref ,fx^) ,@es^)]
      
      [_
        opt-fail])]

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

    ;; Simple reference propogation
    [`(let (ref ,x) (ref ,y) ,body)
      (define eb-env (extend-env env (list x) (list (env-ref env y))))
      (optimize/ast body context eb-env)]

    ;; General let case
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
     (handle-inner-def ast context env)]

    [`(fn (,(or `(ref ,params) `(|...| (ref ,params))) ...) ,anns ,body)
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

          (define new-fn `(fn (,@(map add-ref params^)) ,anns ,body^))

          (fn-rename-annotations new-fn env)]

        ;; Function is in an application context, so try to apply it.
        [(app-context ops c inlined?)
          (define app-result (apply-expr ast context env))

          (if app-result
              app-result
              (optimize/ast ast 'value env))])]

    [`(ref ,x)
      (match-define (var x-sym x-op x-flags x-source-flags) x)

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

          (copy x^ (result op-e) context env)])]

    [(or `(extern-ref ,x) `(fallback-ref ,x))
     (inc-size-total! env)
     (cond
        [(test-context? context) '(const true)]
        [(effect-context? context) '(const void)]
        [else ast])]

    [`(blessed-prim ,x)
      (cond
        ;; Application context, so try to apply the primitive.
        [(app-context? context)
          (match-define (app-context ops outer-context inlined?) context)
          (define op-es (map (lambda (op) (visit-op op 'value)) ops))
          (match (map result op-es)
            ;; All the args are constant, so just apply the primitive.
            [(list `(const ,cs) ...) #:when (hash-has-key? bless-primitives x)
              (define p-fun (hash-ref bless-primitives x))
              (define new-c (apply p-fun cs)) ;; TODO: Should probably check for arity errors here
              (set-box! inlined? #t)
              (inc-size-total! env)
              `(const ,new-c)]

            ;; Otherwise, just leave the primitive application alone.
            [_
              (inc-size-total! env)
              `(blessed-prim ,x)])]
        
        [else
          (error 'inlining "blessed-prim should only occur in an application context: ~a" ast)])]

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
      [inlined?
        ef^]

      ;; ef has not been inlined, so process the operands and then return the call expression
      [else
        (define op-es (map (lambda (op) (visit-op op 'value)) ops))

        (inc-size-total! env)
        (for ([op ops])
          (accumulate-size-total! env (get-env-size-total (unbox (opnd-env op)))))

        `(,ef^ ,@op-es)])]))

(define (handle-inner-def ast context env)
  (define-values (defs more) (get-nested-sibling-defs ast))

  (define fxs
    (for/list ([def (in-list defs)])
      (match-define `(def ((ref ,fx) ,params ...) ,anns ... ,bod) def)
      fx))

  (define fn-vals
    (for/list ([def (in-list defs)])
      (match-define `(def ((ref ,fx) ,params ...) ,anns ... ,body) def)
      `(fn (,@params) (,@anns) ,body)))

  (define fx-ops (construct-operands fn-vals env))
  (define fxs^ (copy-variables fxs))
  (define fxs^-with-op (map (lambda (fx^ op) (variable-set-op fx^ op)) fxs^ fx-ops))

  ;; Optimize `more` with each `fx` mapped its corresponding `fx^`
  ;; We need to use try-optimize since propogating may increase size or effort too much.
  (define more^
    (try-optimize env
      (lambda (env^)
        (define more-env-with-op (extend-env-circular env^ fxs fxs^-with-op))
        (optimize/ast more (replace-app-context context 'value) more-env-with-op))
      (lambda () ;; On abort:
        (define more-env (extend-env env fxs fxs^)) ;; Optimize without the operands bound

        ;; The old ops have an incorrect environment, so create new ones
        (set! fx-ops (construct-operands fn-vals more-env))

        (optimize/ast more (replace-app-context context 'value) more-env))))

  (define fx-op-es (map (lambda (op) (visit-op op 'value)) fx-ops))

  ;; --- Prune unreferenced fx's

  (define more-symb (gensym '__more__)) ;; `more` body node in the call graph
  (define fx-symbs (map var-name fxs^))

  ;; Sibling calls graph with the `more` body included
  (define sibling-calls-graph
    (for/hash ([expr (cons more^ fx-op-es)]
               [node (cons more-symb fx-symbs)])
      (define refs (get-references expr))
      (define sibling-refs (filter (lambda (gx) (member gx fx-symbs)) (set->list refs)))

      (values node sibling-refs)))

  (define reachability-graph (transitive-closure sibling-calls-graph))
  (define reachable-from-more (hash-ref reachability-graph more-symb))

  (define (reachable-from-more? fx)
    (set-member? reachable-from-more fx))

  (define-values (fxs-pruned fx-op-es-pruned)
    (for/fold ([fxs-pruned (list)]
               [fx-op-es-pruned (list)])
              ([fx^ (in-list fxs^)]
               [fx-op-e (in-list fx-op-es)])
      (if (reachable-from-more? (var-name fx^))
          (values (append fxs-pruned (list fx^))
                  (append fx-op-es-pruned (list fx-op-e)))
          
          (values fxs-pruned fx-op-es-pruned))))

  (inc-size-total! env)
  ;; TODO: take the pruning into account:
  (for ([op (in-list fx-ops)])
    (accumulate-size-total! env (get-env-size-total (unbox (opnd-env op)))))

  ;; Reconstruct newly optimized defs
  (define defs^
    (for/list ([op-e (in-list fx-op-es-pruned)]
               [fx (in-list fxs-pruned)])
      (match-define `(fn (,params^ ...) ,anns ,body^) op-e)

      `(def ((ref ,fx) ,@params^) ,@anns ,body^)))
  
  (nest-sibling-defs defs^ more^))

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

  ;; TODO: temp hack for constants
  (define is-good?
    (match e
      [`((extern-ref _init_from_s64) ,a ,b ,c ,d) #t]
      [_ #f]))

  (cond
    ;; Propogate constants
    [(equal? e-tag 'const)
      (optimize/ast e context env)]

    ;; Small enough bless
    [(and (equal? e-tag 'bless) (small-bless? e))
      (if (get-env-under-blessed? env)
          ;; Already under a bless, so just propogate the inner expression
          (match e
            [`(bless ,e0)
             (optimize/ast e0 context env)])
          
          ;; Not under a bless, so propogate the bless tag
          (optimize/ast e context env))]

    [is-good?
      (optimize/ast e context env)]

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

;; `(fn ...) AppContext Environment -> (or Expr #f)
;; Tries to apply a function.
(define (apply-expr expr context env)
  (match expr
    [`(fn (,params ...) ,anns ,body)
      (try-optimize env
        (lambda (env^)
          (apply-fn expr context env^))
        (lambda () ;; On abort:
          #f))]))

;; `(fn ...) AppContext Environment -> (or Expr #f)
(define (apply-fn expr context env)
  (match-define (app-context ops outer-context inlined?) context)
  (match-define `(fn ((ref ,params) ...) ,annotations ,body) expr)

  (define params^ (map (lambda (p^ op) (variable-set-op p^ op)) (copy-variables params) ops))
  (define body-env (extend-env env params params^))

  ;; This may propogate operands into the body
  (define body^ (optimize/ast body outer-context body-env))

  (define can-apply #t)
  (define op-es
    (for/list ([p params^])
      (match-define (var p-sym p-op p-flags p-source-flags) p)

      (define p-is-ref (set-member? p-flags 'ref))
      (define p-is-assign (set-member? p-flags 'assign))

      (cond
        ;; There are no more references to the parameter. So, this
        ;; operand does not prevent us from applying the function.
        [(not p-is-ref)
          (visit-op p-op 'effect)]

        ;; There are references to the parameter still,
        ;; so we cannot apply.
        [else
          (set! can-apply #f)
          (visit-op p-op 'value)])))

  (if can-apply
      (begin
        (set-box! inlined? #t)

        (inc-size-total! env)
        (for ([op ops])
          (accumulate-size-total! env (get-env-size-total (unbox (opnd-env op)))))

        (apply make-seq (append op-es (list body^))))
      
      #f))

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

(define (small-bless? expr)
  (match expr
    [`(bless (const ,c)) #t]
    [_ #f]))

(define (fn-rename-annotations fn env)
  (match-define `(fn ,params ,annotations ,body) fn)
  
  (define fail-to-ann (get-annotation annotations 'fail_to))

  (cond
    [fail-to-ann
      (match-define `((ref ,x)) fail-to-ann)

      (define x^ ;; TODO
        (if (hash-has-key? (environment-bindings env) x)
            (var-name (hash-ref (environment-bindings env) x))
            x))
      
      (define annotations^ (set-annotation annotations 'fail_to (list `(ref ,x^))))

      `(fn ,params ,annotations^ ,body)]
    [else `(fn ,params ,annotations ,body)]))

;; Expr -> (SetOf Symbol)
;; Gets references inside the expr. Assuming everything is alphatized.
;; TODO: ideally this should not be needed. Should be able to calculate reference set during the main walk over the ast.
(define (get-references expr)
  (define (recur-es es)
    (foldl (lambda (e acc)
              (set-union acc (get-references e)))
           (set) es))

  (match expr
    [`(const ,c) (set)]

    [`(bless ,e0) (get-references e0)]

    [`(seq ,e1 ,e2) (set-union (get-references e1) (get-references e2))]

    [`(if ,g ,e1 ,e2) (set-union (get-references g) (get-references e1) (get-references e2))]

    [`(continue-dispatch ,es ...)
      (recur-es es)]
    
    [`(fail ,fx ,es ...)
      (recur-es (cons fx es))]

    ;; TODO:
    [`(fail) (set)]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (get-references e0)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-es es)]

    [`(let (ref ,x) ,rhs ,body)
     (set-union (get-references rhs) (get-references body))]

    [`(|[]| ,es ...)
     (recur-es es)]

    [`(def ((ref ,fx) ,params ...) ,anns ... ,body ,more)
     (set-union (get-references body) (get-references more))]

    [`(fn (,(or `(ref ,params) `(|...| (ref ,params))) ...) ,anns ,body)
     (get-references body)]

    [`(ref ,x)
      (set (var-name x))]

    [(or `(extern-ref ,x) `(fallback-ref ,x))
      (set x)]

    [`((blessed-prim ,x) ,es ...)
      (recur-es es)]

    ;; Untagged application
    [`(,ef ,es ...)
     (recur-es (cons ef es))]))

;; Expr [HashOf Var Var] [Bool] [(or Expr #f)] -> Expr
;; Add extra data to the AST for optimization purposes (e.g. variable locations, flags, etc.).
(define (insert-ast-annotations ast [env (hash)] [under-blessed? #f] [fail-expr #f])
  (define (recur ast)
    (insert-ast-annotations ast env under-blessed? fail-expr))
  (define (recur-with-env ast env)
    (insert-ast-annotations ast env under-blessed? fail-expr))

  (match ast
    [`(const ,c) `(const ,c)]

    [`(bless ,e0)
      `(bless ,(insert-ast-annotations e0 env #t fail-expr))]

    [`(if ,g ,t ,e)
     `(if ,(recur g) ,(recur t) ,(recur e))]

    [`(continue-dispatch ,es ...)
     `(continue-dispatch ,@(map recur es))]
    
    [`(fail)
     (if fail-expr
         fail-expr
         `(fail))]

    [`(,ell ,e0) #:when (eq? ell '|...|)
     `(,ell ,(recur e0))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      `(,ctor ,@(map recur es))]

    [`(let (ref ,x) ,rhs ,body)
      (define new-x (new-variable x))
      (define env-body (hash-set env x new-x))

      `(let (ref ,new-x) ,(recur rhs) ,(recur-with-env body env-body))]

    [`(|[]| ,es ...)
     `(|[]| ,@(map recur es))]

    ;; Inner def
    [`(def ((ref ,fx) ,params ...) ,anns ... ,body ,more)
     (define-values (defs rest-ast) (get-nested-sibling-defs ast))

     (define-values (fx-vars rest-ast-env)
      (for/fold ([fx-vars (list)]
                 [env^ env])
                ([def defs])
        (match-define `(def ((ref ,fx) ,params ...) ,anns ... ,body) def)
        (define fx-var (new-variable fx))

        (values
          (append fx-vars (list fx-var))
          (hash-set env^ fx fx-var))))

     (define defs^
      (for/list ([def defs]
                 [fx-var fx-vars])
        (match-define `(def ((ref ,fx) ,params ...) ,anns ... ,body) def)
        
        (define-values (body-env new-params)
          (for/foldr ([body-env rest-ast-env]
                      [new-params (list)])
                    ([param params])
            
            (define new-param (apply-to-ref-sym param new-variable))
            (values (hash-set body-env (remove-param-ref param) (remove-param-ref new-param))
                    (cons new-param new-params))))

        (define maybe-fail-expr
          (let* ([maybe-fail-to (get-annotation anns 'fail_to)]
                 [maybe-fail-to-x (if maybe-fail-to (second (car maybe-fail-to)) #f)]
                 [maybe-fail-to-var (hash-ref rest-ast-env maybe-fail-to-x #f)])
            (if maybe-fail-to-var
              `(fail (ref ,maybe-fail-to-var) ,@new-params)
              #f)))
          
        `(def ((ref ,fx-var) ,@new-params) ,@anns
          ,(insert-ast-annotations body body-env under-blessed? maybe-fail-expr))))
    
     (nest-sibling-defs defs^ (insert-ast-annotations rest-ast rest-ast-env under-blessed? fail-expr))]

    [`((ref ,blessed-fx) ,es ...) #:when under-blessed?
      `((blessed-prim ,blessed-fx) ,@(map recur es))]

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

    [`(bless ,e0) `(bless ,(recur e0))]
    
    [`(seq ,e1 ,e2)
      (define seq-x (gensym 'seq))
      `(let (ref ,seq-x) ,(recur e1)
            ,(recur e2))]

    [`(if ,g ,t ,e)
     `(if ,(recur g) ,(recur t) ,(recur e))]

    [`(continue-dispatch ,es ...)
     `(continue-dispatch ,@(map recur es))]
    
    ;; TODO:
    [`(fail ,fx ,es ...)
     `(fail)]

    [`(fail)
     `(fail)]

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

    [`(blessed-prim ,x)
     `(ref ,x)]

    ;; Untagged application
    [`(,fe ,es ...)
     `(,(recur fe) ,@(map recur es))]))