#lang racket

(define p1
  `((lambda (x) x) 5))

(define p2
  `(lambda (a)
    (let x 3
      (if (zero? a)
          x
          5))))

(define p3
  `((lambda (x)
      ((lambda (f)
        (f 6))
       (lambda (y)
        (x y))))
    (lambda (z) z)))

(define p4
  `((lambda (x)
      ((lambda (f)
        (f 6))
       (lambda (y)
        (add1 (x y)))))
    (lambda (z) z)))

(define p5
  `(((lambda (x)
      (lambda (y)
        (if (zero? y)
            (x y)
            (add1 (x y)))))
    (lambda (z) z))
    1))

(define p6
 '(let f (lambda (g) (g g))
    (let z (lambda (n) (if (< n 10) (lambda (x) 5) (lambda (x) 15)))
      (let y (lambda (m) (m 4))
        (let x (y z)
          (+ 7 (f x)))))))

(define p7
  `(let f (lambda (a b)
            (a b))
      (f (lambda (x) x) 1)))

(define p8
 '(lambda (h)
    (let f (lambda (g) (g g))
      (let z (lambda (n) (if (< n 10) (lambda (x) 5) (lambda (x) 15)))
        (let y (lambda (m) (m 4))
          (let x (h (y z))
            (+ 7 (f x))))))))

(define primitives (hash 'add1 add1
                         'zero? zero?
                         '+ +
                         '< <))

(struct store
  [var-flags
   context-flags
   exp-cache]
  #:transparent)

(define global-store (store (hash) (hash) (hash)))

(define (store-var-flags-ref loc)
  (hash-ref (store-var-flags global-store) loc))

(define (store-context-flags-ref loc)
  (hash-ref (store-context-flags global-store) loc))

(define (store-exp-cache-ref loc)
  (hash-ref (store-exp-cache global-store) loc))

(define (store-set-var-flags! loc val)
  (set! global-store
    (store
      (hash-set (store-var-flags global-store) loc val)
      (store-context-flags global-store)
      (store-exp-cache global-store))))

(define (store-set-context-flags! loc val)
  (set! global-store
    (store
      (store-var-flags global-store)
      (hash-set (store-context-flags global-store) loc val)
      (store-exp-cache global-store))))

(define (store-set-exp-cache! loc val)
  (set! global-store
    (store
      (store-var-flags global-store)
      (store-context-flags global-store)
      (hash-set (store-exp-cache global-store) loc val))))

(define (mark-inlined! context-loc)
  (store-set-context-flags! context-loc (set-add (store-context-flags-ref context-loc) 'inlined)))


(struct opnd
  [exps
   env
   cache-loc]
  #:transparent)

(define (construct-operand e env)
  (define cache-loc (fresh-loc))

  ;; initialize cache
  (store-set-exp-cache! cache-loc 'unvisited)

  (opnd e env cache-loc))

(define (construct-operands exps env)
  (map (lambda (e) (construct-operand e env)) exps))

(define next-loc 0)
(define (fresh-loc)
  (let ([loc next-loc])
    (set! next-loc (+ next-loc 1))
    loc))

;; Expr -> Expr
(define (optimize-prog prog [recur-count 5])
  (set! global-store (store (hash) (hash) (hash)))

  (define (opt-helper prog recur-count)
    (cond
      [(<= recur-count 0) prog]
      [else
        (displayln (remove-extra-data prog))
        (define prog^ (optimize prog 'value (hash)))

        (if (alpha-equiv? prog prog^)
            prog
            (opt-helper prog^ (- recur-count 1)))]))

  (remove-extra-data (opt-helper (init-extra-data prog) recur-count)))

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
    [`(lambda (,x) ,e)
      (define x^ (gen-sym))
      (define e-env (hash-set env x x^))
      `(lambda (,x^) ,(recur e e-env))]

    [`(let ,x ,e ,be)
      (recur `((lambda (,x) ,be) ,e) env)]

    [`(if ,g ,e1 ,e2)
     `(if ,(recur g env) ,(recur e1 env) ,(recur e2 env))]

    [`(seq ,e1 ,e2)
     `(seq ,(recur e1 env) ,(recur e2 env))]

    [`(,e1 ,e2)
     `(,(recur e1 env) ,(recur e2 env))]

    [(? symbol? p) #:when (set-member? (hash-keys primitives) p)
     p]

    [(? symbol? x)
     (hash-ref env x)]

    [_
     p]))

(define (alpha-equiv? p0 p1)
  (equal? (alphatize (remove-extra-data p0)) (alphatize (remove-extra-data p1))))

(define (copy-variable x)
  (match-define `(var ,x-sym ,op ,s ,loc-x) x)
  (define loc-x^ (fresh-loc))
  (define x^ `(var ,(gensym x-sym) ,op ,(store-var-flags-ref loc-x) ,loc-x^))

  (store-set-var-flags! loc-x^ (set))

  x^)

;; (ListOf Varable) -> (ListOf Variable)
(define (copy-variables xs)
  (map copy-variable xs))

(define (extend-env env xs xs^)
  (for/fold ([env env])
            ([x xs]
             [x^ xs^])
    (hash-set env x x^)))

(define (new-variable x-sym)
  (define x-loc (fresh-loc))
  (define x `(var ,x-sym null ,(set) ,x-loc))
  (store-set-var-flags! x-loc (set))

  x)

(define (variable-set-op x op)
  (match-define `(var ,x-sym ,_ ,s ,loc-x) x)
  `(var ,x-sym ,op ,s ,loc-x))

;; Expr Context Env -> Expr
;; Mutates the global store as it goes; returns the optimized expression
;; directly instead of invoking a continuation.
(define (optimize expr context env)
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
          [`(app ,op ,c ,loc) 'value]
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
        [`(app ,ops ,c ,loc)
          (fold-expr expr context env)])]

    [`(call ,ef ,args ...)
      ;; Create application context for ef so that the processing of ef can
      ;; perform inlining if possible.
      (define ops (construct-operands args env))

      (define loc-ef-context (fresh-loc))
      (define ef-context `(app ,ops ,context ,loc-ef-context))

      (store-set-context-flags! loc-ef-context (set)) ;; initalize ef context flags

      (define ef^ (optimize ef ef-context env))
      (define context-flags (store-context-flags-ref loc-ef-context))

      (cond
        ;; ef has been inlined (so ignore the operands and just return the inlined result)
        [(set-member? context-flags 'inlined) ef^]

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
      (match-define `(var ,x-sym ,x-op ,x-source-flags ,x-loc) x)

      (define x^ (hash-ref env x))
      (match-define `(var ,x^-sym ,op ,x^-source-flags ,x^-loc) x^)

      (cond
        ;; If in an effect context, then we don't care about the reference
        [(equal? context 'effect)
          '(const void)]

        ;; If x^ is not bound to an operand or it is a mutable reference,
        ;; then we can't inline/propogate it.
        [(or (equal? op 'null)
             (set-member? x^-source-flags 'assign))
          ;; Mark it as a ref if it wasn't already.
          (store-set-var-flags! x^-loc (set-add (store-var-flags-ref x^-loc) 'ref))

          `(ref ,x^)]

        ;; Otherwise, we can try to copy/propogate the value of x^ into the reference site.
        [else
          ;; Get the operand expression and then try to copy it to the reference site.
          (define op-e (visit-op op 'value))
          (copy x^ (result op-e) context)])]))

;; Residualize an operand/argument expression (if it has already been visited,
;; it will use the cached version)
(define (visit-op op context)
  (match-define (opnd e env e-loc) op)
  (define cached (store-exp-cache-ref e-loc))

  (cond
    ;; We need to process the operand expression for the first time (cache is empty).
    [(equal? cached 'unvisited)
      (define e^ (optimize e context env))
      (store-set-exp-cache! e-loc e^)
      e^]

    ;; Otherwise, we have already processed the operand, so just use the cached version.
    [else cached]))

;; Helper to sequence expressions (ensuring that the
;; last expression in the sequence is not a sequence itself).
(define (make-seq e1 e2 . es)
  (define (make-seq-pair e1 e2)
    (match* (e1 e2)
      [('(const void) _) e2]
      [(_ `(seq ,e3 ,e4)) `(seq (seq ,e1 ,e3) ,e4)]
      [(_ _) `(seq ,e1 ,e2)]))

  ;; Note: for more than two expression, void constants may not be removed here.
  (if (null? es)
      (make-seq-pair e1 e2)
      (apply make-seq (make-seq-pair e1 e2) es)))

;; Helper to ignore sequence expressions and just return the last expression in the sequence.
(define (result e)
  (match e
    [`(seq ,_ ,e2) e2]
    [else e]))

;; Handles copy propogation and inlining at a variable reference site.
;; x-var is the variable reference site. e is the expression that x-var refers to.
(define (copy x-var e context)
  (match-define `(var ,x ,op ,s ,loc-x) x-var)

  (define e-tag (car e))

  (define context-type
    (match context
      [`(app ,op ,c ,loc) 'app]
      [_ context]))

  (define immutable-var-ref?
    (if (equal? e-tag 'ref)
        (match-let ([`(ref ,y-var) e])
          (match-define `(var ,y ,op-y ,s-y ,loc-y) y-var)
          (not (set-member? s-y 'assign)))
        #f))

  (cond
    ;; Propogate constants
    [(equal? e-tag 'const)
      (match-define `(const ,c) e)
      (optimize `(const ,c) context (hash))]

    ;; Propogate immutable variables
    [immutable-var-ref?
      (match-define `(ref ,y-var) e)
      (match-define `(var ,y ,op-y ,s-y ,loc-y) y-var)

      `(ref ,y-var)]

    ;; Inline lambdas and primitive references into application contexts and try to beta reduce them?
    [(and (equal? context-type 'app) (or (equal? e-tag 'lambda) (equal? e-tag 'primref)))
      (match-define `(app ,op ,c ,loc) context)
      (fold-expr e context (hash))]

    ;; A primref is basically a constant. So just propogate it.
    [(and (equal? context-type 'value) (equal? e-tag 'primref))
      e]

    ;; Lambdas, assignments, and primitive references are truthy (so the variable ref
    ;; to them can be replaced with #t)
    [(and (equal? context-type 'test)
          (or (equal? e-tag 'lambda) (equal? e-tag 'assign) (equal? e-tag 'primref)))
      '(const #t)]

    ;; Otherwise, just leave the reference alone (mark it as a reference if needed).
    [else
      (store-set-var-flags! loc-x (set-add (store-var-flags-ref loc-x) 'ref))
      `(ref ,x-var)]))

;; Tries to reduce an application of a lambda or primitive.
(define (fold-expr expr context env)
  (match expr
    [`(primref ,p)
      (match-define `(app ,ops ,app-context ,context-loc) context)
      (define op-es (map (lambda (op) (visit-op op 'value)) ops))
      (match (map result op-es)
        ;; All the args are constant, so just apply the primitive.
        [(list `(const ,cs) ...)
         (define p-fun (hash-ref primitives p))
         (define new-c (apply p-fun cs)) ;; Note: Should probably check for arity errors here
         (mark-inlined! context-loc)
         `(const ,new-c)]

        ;; Otherwise, just leave the primitive application alone.
        [_
          `(primref ,p)])]
    [`(lambda (,params ...) ,eb)
      (fold-lambda expr context env)]))

;; Try beta reducing the lambda
(define (fold-lambda expr context env)
  (match-define `(app ,ops ,app-context ,context-loc) context)
  (match-define `(lambda (,params ...) ,eb) expr)

  (define params^ (copy-variables params))
  (define params^^ (map (lambda (p^ op) (variable-set-op p^ op)) params^ ops))
  (define eb-env (extend-env env params params^^))

  ;; This may propogate operands into the body
  (define eb^ (optimize eb app-context eb-env))

  (define can-reduce #t)
  (define op-es
    (for/list ([p params^^])
      (match-define `(var ,p-sym ,op ,s ,loc-p) p)

      (define p-flags (store-var-flags-ref loc-p))
      (define p-is-ref (set-member? p-flags 'ref))
      (define p-is-assign (set-member? p-flags 'assign))

      (cond
        ;; There are no more references to the parameter. So, this
        ;; operand does not prevent us from beta reducing the lambda.
        [(and (not p-is-ref) (not p-is-assign))
          (visit-op op 'effect)]

        ;; There are references or assignments to the parameter still,
        ;; so we cannot beta reduce.
        [(and (not p-is-ref) p-is-assign)
          (set! can-reduce #f)
          (visit-op op 'effect)]
        [else
          (set! can-reduce #f)
          (visit-op op 'value)])))
  
  (mark-inlined! context-loc)
  (if can-reduce
      (apply make-seq (append op-es (list eb^)))
      `(call (lambda (,@params^^) ,eb^) ,@op-es)))

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

    [`(let ,x ,e ,be)
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
    [`(var ,x ,op ,s ,loc-x) x]

    [`(const ,c) c]

    [`(seq ,e1 ,e2)
     `(seq ,(remove-extra-data e1) ,(remove-extra-data e2))]

    [`(if ,g ,e1 ,e2)
     `(if ,(remove-extra-data g) ,(remove-extra-data e1) ,(remove-extra-data e2))]
    
    [`(call (lambda (,x) ,eb) ,e)
     `(let ,(remove-extra-data x) ,(remove-extra-data e) ,(remove-extra-data eb))]

    [`(lambda (,params ...) ,eb)
      `(lambda (,@(map remove-extra-data params)) ,(remove-extra-data eb))]

    [`(call ,ef ,args ...)
     `(,(remove-extra-data ef) ,@(map (lambda (arg) (remove-extra-data arg)) args))]

    [`(primref ,p)
     p]

    [`(ref ,x)
     (remove-extra-data x)]))
