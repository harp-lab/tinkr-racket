#lang racket

(provide optimize-prog
         effort-bound
         set-effort-bound!
         alphatize)

;; NOTES:
;;  - When aborting an inlining attempt, var structures are not reset to the original state in
;;    any way. This could cause problems later on.

;; Parameters
(define effort-bound 50)
(define (set-effort-bound! v) (set! effort-bound v))


;; A Context is one of 'effect, 'test, 'value, or an AppContext

(struct opnd
  [exp     ;; Expr
   env     ;; (HashOf Var Var)
   cache]  ;; (BoxOf Expr)
  #:transparent)

(struct var
  [name           ;; Symbol
   op             ;; Opnd
   flags          ;; (MutableSetOf VarFlag)
   source-flags]  ;; (SetOf VarFlag)
  #:transparent)
;; Where VarFlag can be one of 'ref or 'assign

(struct app-context
  [ops            ;; (ListOf Opnd)
   outer-context  ;; Context
   inlined?]      ;; (BoxOf Bool)
  #:transparent)

(struct environment
  [bindings         ;; (HashOf Var Var)
   effort-counter   ;; (or #f (BoxOf Integer))
   abort-kont]      ;; (or #f Continuation)
  #:transparent)

(define primitives (hash 'add1 add1
                         'zero? zero?
                         '+ +
                         '- -
                         '* *
                         '< <))

;; Expr -> Expr
(define (optimize-prog prog [recur-count 5])
  (define (opt-helper prog recur-count)
    (cond
      [(<= recur-count 0) prog]
      [else
        (define prog^ (optimize prog 'value (environment (hash) #f #f)))

        (if (alpha-equiv? prog prog^)
            prog
            (opt-helper prog^ (- recur-count 1)))]))

  (remove-extra-data (opt-helper (init-extra-data prog) recur-count)))

(define (construct-operands exps env)
  (map (lambda (e) (opnd e env (box #f))) exps))

(define (make-gensym sym)
  (define count 0)
  (lambda ()
    (set! count (+ count 1))
    (string->symbol
      (string-append (symbol->string sym)
                     (number->string count)))))

(define (alphatize p [env (hash)] [gen-sym (make-gensym 'x)])
  (define (recur p env)
    (alphatize p env gen-sym))

  (match p
    ['void 'void]
    [(? number? n) n]
    [(? boolean? b) b]
    [(? string? s) s]
    [`(primref ,p) `(primref ,p)]

    [`(lambda (,params ...) ,eb)
      (define params^ (map (lambda (x) (gen-sym)) params))
      (define eb-env
        (for/fold ([eb-env env])
                  ([x params]
                   [x^ params^])
          (hash-set eb-env x x^)))
      `(lambda (,@params^) ,(recur eb eb-env))]

    [`(let ([,x ,e]) ,be)
      (recur `((lambda (,x) ,be) ,e) env)]

    [`(if ,g ,e1 ,e2)
     `(if ,(recur g env) ,(recur e1 env) ,(recur e2 env))]

    [`(seq ,e1 ,e2)
     `(seq ,(recur e1 env) ,(recur e2 env))]

    [(? symbol? p) #:when (set-member? (hash-keys primitives) p)
     p]

    [(? symbol? x)
     (hash-ref env x)]

    [`(,ef ,eas ...)
     `(,(recur ef env) ,@(map (lambda (ea) (recur ea env)) eas))]))

(define (alpha-equiv? p0 p1)
  (equal? (alphatize (remove-extra-data p0)) (alphatize (remove-extra-data p1))))

(define (copy-variable x)
  (match-define (var x-sym op flags source-flags) x)
  (define x^ (var (gensym x-sym) op (mutable-set) flags))
  x^)

;; (ListOf Varable) -> (ListOf Variable)
(define (copy-variables xs)
  (map copy-variable xs))

(define (start-counter env do)
  (if (environment-effort-counter env)
      (do env)
      (let/ec kont
        (do (environment
              (environment-bindings env)
              (box 0)
              kont)))))

(define (env-ref env x)
  (hash-ref (environment-bindings env) (var-name x)))

(define (extend-env env xs xs^)
  (define bindings
    (for/fold ([bindings (environment-bindings env)])
              ([x xs]
               [x^ xs^])
      (hash-set bindings (var-name x) x^)))

  (environment
    bindings
    (environment-effort-counter env)
    (environment-abort-kont env)))

(define (get-env-effort env)
  (if (environment-effort-counter env)
      (unbox (environment-effort-counter env))
      #f))
(define (set-env-effort! env effort)
  (when (environment-effort-counter env)
        (set-box! (environment-effort-counter env) effort)))
(define (inc-env-effort! env)
  (define effort (get-env-effort env))
  (if effort
      (set-env-effort! env (add1 effort))
      env))

(define (remove-env-bindings env)
  (environment (hash) (environment-effort-counter env) (environment-abort-kont env)))

(define (abort-inlining-attempt env)
  ((environment-abort-kont env) #f))

(define (new-variable x-sym)
  (var x-sym '() (mutable-set) (set)))

(define (variable-set-op x op)
  (match-define (var x-sym _ flags source-flags) x)
  (var x-sym op flags source-flags))

;; Expr Context Env -> Expr
(define (optimize expr context env)
  (define effort (get-env-effort env))
  (when effort
    (if (< effort effort-bound)
        (inc-env-effort! env)
        (abort-inlining-attempt env)))

  (match expr
    [`(const ,c)
      (cond
        [(equal? context 'effect) '(const void)]

        ;; All values except #f are truthy.
        [(and (equal? context 'test) (not (equal? c #f)))
          '(const #t)]

        ;; We need the value of the constant still
        [else `(const ,c)])]

    ;; Evalutate e1 for its effect, then evaluate e2 for the current context
    [`(seq ,e1 ,e2)
      (define e1^ (optimize e1 'effect env))
      (define e2^ (optimize e2 context env))
      (make-seq e1^ e2^)]

    [`(if ,g ,e1 ,e2)
      (define g^ (optimize g 'test env))
      (define g-res (result g^))

      ;; We don't want to propogate an application context down the if branches
      (define e-context
        (match context
          [(app-context ops c inlined?) 'value]
          [_ context]))

      (cond
        ;; Always go down the true branch
        [(equal? g-res '(const #t))
         (define e1^ (optimize e1 e-context env))
         (make-seq g^ e1^)]

        ;; Always go down the false branch
        [(equal? g-res '(const #f))
         (define e2^ (optimize e2 e-context env))
         (make-seq g^ e2^)]
        
        ;; Could be either branch
        [else
          (define e1^ (optimize e1 e-context env))
          (define e2^ (optimize e2 e-context env))

          (match* (e1^ e2^)
            ;; Both branches evaluate to the same constant, so just return the constant,
            ;; letting the guard expression be evaluated for just its effect.
            [(`(const ,c1) `(const ,c2)) #:when (equal? c1 c2)
              (make-seq g^ e1^)]
            
            ;; Otherwise, just return the if
            [(_ _)
              `(if ,g^ ,e1^ ,e2^)])])]

    [`(lambda (,params ...) ,eb)
      (match context
        ['test '(const #t)]
        ['effect '(const void)]

        ;; Just leave the lambda alone (and recur down the body)
        ['value
          ;; Create a new variables for the formal parameters.
          (define params^ (copy-variables params))
          (define eb-env (extend-env env params params^))

          (define eb^ (optimize eb 'value eb-env))
          `(lambda (,@params^) ,eb^)]

        ;; Lambda is in an application context, so try to beta reduce (i.e. fold) it.
        [(app-context ops c inlined?)
          (fold-expr expr context env)])]

    [`(call ,ef ,args ...)
      ;; Create an application context for ef so that the processing of ef can
      ;; perform inlining if possible.
      (define ops (construct-operands args env))
      (define ef-context (app-context ops context (box #f)))

      (define ef^ (optimize ef ef-context env))
      (define inlined? (unbox (app-context-inlined? ef-context)))

      (cond
        ;; Ignore the operands and just return the inlined result
        [inlined? ef^]

        ;; ef has not been inlined, so process the operands and then return the call expression
        [else
          (define op-es (map (lambda (op) (visit-op op 'value)) ops))
          `(call ,ef^ ,@op-es)])]

    [`(primref ,x)
      (cond
        [(equal? context 'test) '(const #t)]
        [(equal? context 'effect) '(const void)]
        [(equal? context 'value) `(primref ,x)]

        ;; Application context, so try to apply the primitive.
        [else (fold-expr `(primref ,x) context env)])]

    [`(ref ,x)
      (match-define (var x-sym x-op x-flags x-source-flags) x)

      (define x^ (env-ref env x))
      (match-define (var x^-sym op x^-flags x^-source-flags) x^)

      (cond
        ;; If in an effect context, then we don't care about the reference
        [(equal? context 'effect)
          '(const void)]

        ;; If x^ is not bound to an operand or it is a mutable reference,
        ;; then we can't inline/propogate it.
        [(or (null? op)
             (set-member? x^-source-flags 'assign))
          ;; Mark it as a ref if it wasn't already.
          (set-add! x^-flags 'ref)

          `(ref ,x^)]

        ;; Otherwise, we can try to copy/propogate the value of x^ into the reference site.
        [else
          ;; Get the operand expression and then try to copy it to the reference site.
          (define op-e (visit-op op 'value))
          (copy x^ (result op-e) context env)])]))

;; Residualize an operand/argument expression (if it has already been visited,
;; it will use the cached version)
(define (visit-op op context)
  (match-define (opnd e env cache) op)
  (define c (unbox cache))

  (cond
    ;; We have already processed the operand, so just use the cached version.
    [c c]

    ;; We need to process the operand expression for the first time (cache is #f).
    [else
      (define e^ (optimize e context env))
      (set-box! cache e^)
      e^]))

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

(define (no-effect? expr)
  (match expr
    [`(const ,_) #t]
    [`(primref ,_) #t]
    [`(lambda (,params ...) ,eb) #t]
    [`(ref ,x) #t]
    [_ #f]))

;; Helper to ignore sequence expressions and just return the last expression in the sequence.
(define (result e)
  (match e
    [`(seq ,_ ,e2) e2]
    [else e]))

;; Handles copy propogation and inlining at a variable reference site.
;; x is the variable reference site. e is the expression that x refers to.
(define (copy x e context env)
  (match-define (var x-sym op flags source-flags) x)

  (define e-tag (car e))

  (define context-type
    (match context
      [(app-context ops c inlined?) 'app]
      [_ context]))

  (define immutable-var-ref?
    (if (equal? e-tag 'ref)
        (match-let ([`(ref ,y) e])
          (match-define (var y-sym y-op y-flags y-source-flags) y)
          (not (set-member? y-source-flags 'assign)))
        #f))

  (cond
    ;; Propogate constants
    [(equal? e-tag 'const)
      (match-define `(const ,c) e)
      (optimize `(const ,c) context (remove-env-bindings env))]

    ;; Propogate immutable variables
    [immutable-var-ref?
      (match-define `(ref ,y) e)
      (match-define (var y-sym y-op y-flags y-source-flags) y)

      `(ref ,y)]

    ;; Inline lambdas and primitive references into application contexts and try to beta reduce them
    [(and (equal? context-type 'app) (or (equal? e-tag 'lambda) (equal? e-tag 'primref)))
      (match-define (app-context ops c inlined?) context)
      (fold-expr e context (remove-env-bindings env))]

    ;; A primref is basically a constant. So just propogate it.
    ;; TODO: Why does the paper only allow primref and not lambda, is it
    ;; just for termination purposes?
    [(and (equal? context-type 'value) (or (equal? e-tag 'primref)))
      e]

    ;; Lambdas, assignments, and primitive references are truthy (so the variable ref
    ;; to them can be replaced with #t)
    [(and (equal? context-type 'test)
          (or (equal? e-tag 'lambda) (equal? e-tag 'assign) (equal? e-tag 'primref)))
      '(const #t)]

    ;; Otherwise, just leave the reference alone (mark it as a reference if needed).
    [else
      (set-add! flags 'ref)
      `(ref ,x)]))

;; Tries to reduce an application of a lambda or primitive.
(define (fold-expr expr context env)
  (match expr
    [`(primref ,p)
      (match-define (app-context ops outer-context inlined?) context)
      (define op-es (map (lambda (op) (visit-op op 'value)) ops))
      (match (map result op-es)
        ;; All the args are constant, so just apply the primitive.
        [(list `(const ,cs) ...)
        (define p-fun (hash-ref primitives p))
        (define new-c (apply p-fun cs)) ;; Note: Should probably check for arity errors here
        (set-box! inlined? #t)
        `(const ,new-c)]

        ;; Otherwise, just leave the primitive application alone.
        [_
          `(primref ,p)])]
    [`(lambda (,params ...) ,eb)
      (define rv
        (start-counter env
          (lambda (env^)
            (fold-lambda expr context env^))))
      
      (if rv
          rv

          ;; We must have aborted, so just optimize for value
          (optimize expr 'value env))]))

;; Try beta reducing the lambda
(define (fold-lambda expr context env)
  (match-define (app-context ops outer-context inlined?) context)
  (match-define `(lambda (,params ...) ,eb) expr)

  (define params^ (map (lambda (p^ op) (variable-set-op p^ op)) (copy-variables params) ops))
  (define eb-env (extend-env env params params^))

  ;; This may propogate operands into the body
  (define eb^ (optimize eb outer-context eb-env))

  (define can-reduce #t)
  (define op-es
    (for/list ([p params^])
      (match-define (var p-sym p-op p-flags p-source-flags) p)

      (define p-is-ref (set-member? p-flags 'ref))
      (define p-is-assign (set-member? p-flags 'assign))

      (cond
        ;; There are no more references to the parameter. So, this
        ;; operand does not prevent us from beta reducing the lambda.
        [(and (not p-is-ref) (not p-is-assign))
          (visit-op p-op 'effect)]

        ;; There are references or assignments to the parameter still,
        ;; so we cannot beta reduce.
        [(and (not p-is-ref) p-is-assign)
          (set! can-reduce #f)
          (visit-op p-op 'effect)]
        [else
          (set! can-reduce #f)
          (visit-op p-op 'value)])))
  
  (set-box! inlined? #t)
  (if can-reduce
      (apply make-seq (append op-es (list eb^)))
      `(call (lambda (,@params^) ,eb^) ,@op-es)))

;; Add extra data to the AST for optimization purposes (e.g. variable locations, flags, etc.).
(define (init-extra-data expr [env (hash)])
  (define (recur expr)
    (init-extra-data expr env))

  (match expr
    [(? number? c) `(const ,c)]
    [(? boolean? c) `(const ,c)]
    [(? string? c) `(const ,c)]

    [`(seq ,e1 ,e2)
     `(seq ,(recur e1) ,(recur e2))]

    [`(if ,g ,e1 ,e2)
     `(if ,(recur g) ,(recur e1) ,(recur e2))]

    [`(lambda (,params ...) ,eb)
      (define-values (eb-env new-params)
        (for/foldr ([eb-env env]
                    [new-params (list)])
                   ([param params])
          (define new-param (new-variable param))
          (values (hash-set eb-env param new-param)
                  (cons new-param new-params))))

      `(lambda (,@new-params) ,(init-extra-data eb eb-env))]

    [`(let ([,x ,e]) ,be)
      (recur `((lambda (,x) ,be) ,e))]

    [`(,e1 ,args ...)
     `(call ,(recur e1) ,@(map recur args))]

    [(? symbol? x) #:when (set-member? (hash-keys primitives) x)
     `(primref ,x)]

    [(? symbol? x)
     `(ref ,(hash-ref env x))]))

;; Remove extra data from the AST.
(define (remove-extra-data expr)
  (match expr
    [(var x-sym op flags source-flags) x-sym]

    [`(const ,c) c]

    [`(seq ,e1 ,e2)
     `(seq ,(remove-extra-data e1) ,(remove-extra-data e2))]

    [`(if ,g ,e1 ,e2)
     `(if ,(remove-extra-data g) ,(remove-extra-data e1) ,(remove-extra-data e2))]
    
    [`(call (lambda (,x) ,eb) ,e)
     `(let ([,(remove-extra-data x) ,(remove-extra-data e)]) ,(remove-extra-data eb))]

    [`(lambda (,params ...) ,eb)
      `(lambda (,@(map remove-extra-data params)) ,(remove-extra-data eb))]

    [`(call ,ef ,args ...)
     `(,(remove-extra-data ef) ,@(map (lambda (arg) (remove-extra-data arg)) args))]

    [`(primref ,p)
     p]

    [`(ref ,x)
     (remove-extra-data x)]))
