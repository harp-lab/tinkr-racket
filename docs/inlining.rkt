#lang racket

(define p1
  `((lambda (x) x) 5))

(define p2
  `(let ([x 3])
    (if ((primref =) (ref x) (const 0))
        (ref x)
        (const 5))))

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

(define primitives (hash 'add1 add1
                         'zero? zero?))

(struct store
  [var-flags
   context-flags
   exp-cache]
  #:transparent)

(define (store-var-flags-ref st loc)
  (hash-ref (store-var-flags st) loc))

(define (store-context-flags-ref st loc)
  (hash-ref (store-context-flags st) loc))

(define (store-exp-cache-ref st loc)
  (hash-ref (store-exp-cache st) loc))

(define (store-set-var-flags st loc val)
  (store
    (hash-set (store-var-flags st) loc val)
    (store-context-flags st)
    (store-exp-cache st)))

(define (store-set-context-flags st loc val)
  (store
    (store-var-flags st)
    (hash-set (store-context-flags st) loc val)
    (store-exp-cache st)))

(define (store-set-exp-cache st loc val)
  (store
    (store-var-flags st)
    (store-context-flags st)
    (hash-set (store-exp-cache st) loc val)))



(struct opnd
  [exp
   env
   loc-exp]
  #:transparent)

(define next-loc 0)
(define (fresh-loc)
  (let ([loc next-loc])
    (set! next-loc (+ next-loc 1))
    loc))

(define global-store (store (hash) (hash) (hash)))

;; Expr -> Expr
(define (optimize-prog prog [recur-count 5])
  (define (opt-helper prog recur-count)
    (cond
      [(<= recur-count 0) prog]
      [else
        (displayln (remove-extra-data prog))
        (define prog^ (optimize prog 'value (hash) (lambda (exp st) exp) global-store))

        (if (equal? prog prog^)
            prog
           (opt-helper prog^ (- recur-count 1)))]))

  (remove-extra-data (opt-helper (init-extra-data prog) recur-count)))

(define (new-variable x st)
  (match-define `(var ,x-sym null ,s ,loc-x) x)
  (define loc-x^ (fresh-loc))
  (define x^ `(var ,(gensym x-sym) null ,(store-var-flags-ref st loc-x) ,loc-x^))

  (define st^ (store-set-var-flags st loc-x^ (set)))
  
  (values x^ st^))

(define (optimize expr context env kont st)
  (match expr
    [`(const ,c)
      (cond
        [(equal? context 'effect) (kont '(const void) st)]

        ;; All values except #f are truthy.
        [(and (equal? context 'test) (not (equal? c #f)))
          (kont '(const #t) st)]

        ;; We need the value of the constant still
        [else (kont `(const ,c) st)])]
    
    ;; Evalutate e1 for its effect, then evaluate e2 for the current context
    [`(seq ,e1 ,e2)
      (optimize e1 'effect env
                (lambda (e1^ st^)
                  (optimize e2 context env
                    (lambda (e2^ st^)
                      (kont (make-seq e1^ e2^) st^))
                    st^)) st)]

    [`(lambda (,x) ,e)
      (match context
        ['test (kont `(const #t) st)]
        ['effect (kont `(const void) st)]

        ;; Just leave the lambda alone (and recur down the body)
        ['value
          ;; Create a new variable x^ for the formal parameter
          (define-values (x^ e-st) (new-variable x st))
          (define e-env (hash-set env x x^))

          (optimize e 'value e-env
            (lambda (e^ st^)
              (kont `(lambda (,x^) ,e^) st^))
            e-st)]
        
        ;; Lambda is in an application context, so try to beta reduce (i.e. fold) it.
        [`(app ,op ,c ,loc)
          (fold-expr `(lambda (,x) ,e) context env kont st)])]

    [`(call ,ef ,ea)
      ;; Create application context for ef so that the processing of ef can
      ;; perform inlining if possible.
      (define loc-ea (fresh-loc))
      (define loc-ef-context (fresh-loc))
      (define op (opnd ea env loc-ea))
      (define ef-context `(app ,op ,context ,loc-ef-context))

      (define ef-store (store-set-context-flags
                          (store-set-exp-cache st loc-ea 'unvisited)     ;; initialize ea cache
                                                  loc-ef-context (set))) ;; initalize ef context flags

      (optimize ef ef-context env
        (lambda (ef^ ef-store^)
          (define context-flags (store-context-flags-ref ef-store^ loc-ef-context))
          (cond
            ;; ef has been inlined (so ignore ea and just return the inlined result)
            [(set-member? context-flags 'inlined) (kont ef^ ef-store^)]

            ;; ef has not been inlined, so process ea (via visiting op) and then return the call expression
            [else
              (visit op 'value
                    (lambda (ea^ ea-store^) (kont `(call ,ef^ ,ea^) ea-store^))
                    ef-store^)]))
        ef-store)]
    
    [`(primref ,x)
      (cond
        [(equal? context 'test) (kont `(const #t) st)]
        [(equal? context 'effect) (kont `(const void) st)]
        [(equal? context 'value) (kont `(primref ,x) st)]
        
        ;; Application context, so try to apply the primitive.
        [else (fold-expr `(primref ,x) context env kont st)])]

    [`(ref ,x)
      (match-define `(var ,x-sym null ,x-source-flags ,x-loc) x)

      (define x^ (hash-ref env x))
      (match-define `(var ,x^-sym ,op ,x^-source-flags ,x^-loc) x^)

      (cond
        ;; If in an effect context, then we don't care about the reference
        [(equal? context 'effect)
          (kont `(const void) st)]
        
        ;; If x^ is not bound to an operand or it is a mutable reference,
        ;; then we can't inline/propogate it.
        [(or (equal? op 'null)
             (set-member? x^-source-flags 'assign))
          ;; Mark it as a ref if it wasn't already.
          (define x^-var-flags (store-var-flags-ref st x^-loc))
          (define st^ (store-set-var-flags st x^-loc (set-add x^-var-flags 'ref)))
          
          (kont `(ref ,x^) st^)]
        
        ;; Otherwise, we can try to copy/propogate the value of x^ into the reference site.
        [else
          ;; Get the operand expression and then try to copy it to the reference site.
          (visit op 'value
                 (lambda (op-e st^)
                   (copy x^ (result op-e) context kont st^)) st)])]))

;; Residualize an operand/argument expression (if it has already been visited,
;; it will use the cached version)
(define (visit op context kont st)
  (match-define (opnd e env e-loc) op)
  (define cached (store-exp-cache-ref st e-loc))

  (cond
    ;; We need to process the operand expression for the first time (cache is empty).
    [(equal? cached 'unvisited)
      (define new-kont
        (lambda (e^ st^)
          (kont e^ (store-set-exp-cache st^ e-loc e^))))

      (optimize e context env new-kont st)]
    
    ;; Otherwise, we have already processed the operand, so just use the cached version.
    [else (kont cached st)]))

;; Helper to sequence two expressions (ensuring that the
;; last expression in the sequence is not a sequence itself).
(define (make-seq e1 e2)
  (match* (e1 e2)
    [('(const void) _) e2]
    [(_ `(seq ,e3 ,e4)) `(seq (seq ,e1 ,e3) ,e4)]
    [(_ _) `(seq ,e1 ,e2)]))

;; Helper to ignore sequence expressions and just return the last expression in the sequence.
(define (result e)
  (match e
    [`(seq ,_ ,e2) e2]
    [else e]))

;; Handles copy propogation and inlining at a variable reference site.
;; x-var is the variable reference site. e is the expression that x-var refers to.
(define (copy x-var e context kont st)
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
      (optimize `(const ,c) context (hash) kont st)]
    
    ;; Propogate immutable variables
    [immutable-var-ref?
      (match-define `(ref ,y-var) e)
      (match-define `(var ,y ,op-y ,s-y ,loc-y) y-var)

      (kont `(ref ,y-var) st)]
    
    ;; Inline lambdas and primitive references into application contexts and try to beta reduce them?
    [(and (equal? context-type 'app) (or (equal? e-tag 'lambda) (equal? e-tag 'primref)))
      (match-define `(app ,op ,c ,loc) context)
      (fold-expr e context (hash) kont st)]
    
    ;; A primref is basically a constant. So just propogate it.
    [(and (equal? context-type 'value) (equal? e-tag 'primref))
      (kont e st)]
    
    ;; Lambdas, assignments, and primitive references are truthy (so the variable ref
    ;; to them can be replaced with #t)
    [(and (equal? context-type 'test)
          (or (equal? e-tag 'lambda) (equal? e-tag 'assign) (equal? e-tag 'primref)))
      (kont `(const #t) st)]
    
    ;; Otherwise, just leave the reference alone (mark it as a reference if needed).
    [else
      (define st^ (store-set-var-flags st loc-x (set-add (store-var-flags-ref st loc-x) 'ref)))
      (kont `(ref x-var) st^)]))

;; Tries to reduce an application of a lambda or primitive.
(define (fold-expr expr context env kont st)
  (match expr
    [`(primref ,p)
      (match-define `(app ,op ,app-context ,context-loc) context)
      (visit op 'value
            (lambda (op-e st)
              (match (result op-e)
                ;; Arg is a constant, so just apply the primitive.
                [`(const ,c)
                 (define p-fun (hash-ref primitives p))
                 (define new-c (p-fun c))
                 (define st^ (store-set-context-flags st context-loc (set-add (store-context-flags-ref st context-loc) 'inlined)))
                 (kont `(const ,new-c) st^)]
                
                ;; Otherwise, just leave the primitive application alone.
                [_
                  (kont `(primref ,p) st)]))
            st)]
    [`(lambda (,x) ,e)
      (fold-lambda expr context env kont st)]))

;; Try beta reducing the lambda
(define (fold-lambda expr context env kont st)
  (match-define `(app ,op ,app-context ,context-loc) context)
  (match-define `(lambda (,x-var) ,e) expr)

  (match-define `(var ,x null ,s ,loc-x) x-var)
  (define loc-x^ (fresh-loc))
  (define x^-var `(var ,(gensym x) ,op ,(store-var-flags-ref st loc-x) ,loc-x^))

  (define e-env (hash-set env x-var x^-var))
  (define e-st (store-set-var-flags st loc-x^ (set)))
  (define e-kont
    (lambda (e^ st^)
      (define x^-flags (store-var-flags-ref st^ loc-x^))
      (define x^-is-ref (set-member? x^-flags 'ref))
      (define x^-is-assign (set-member? x^-flags 'assign))

      (define k2
        (lambda (e1^ st3)
          (define st3^ (store-set-context-flags st3 context-loc (set-add (store-context-flags-ref st3 context-loc) 'inlined)))
          (kont `(seq ,e1^ ,e^) st3^)))

      (define k3
        (lambda (e1^ st3)
          (define st3^ (store-set-context-flags st3 context-loc (set-add (store-context-flags-ref st3 context-loc) 'inlined)))
          (kont `(call (lambda (,x^-var) ,e^) ,e1^) st3^)))

      (cond
        [(and (not x^-is-ref) (not x^-is-assign))
          (visit op 'effect k2 st^)]
        [(and (not x^-is-ref) x^-is-assign)
          (visit op 'effect k3 st^)]
        [else
          (visit op 'value k3 st^)])))

  (optimize e app-context e-env e-kont e-st))

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

    [`(lambda (,x) ,e)
      (define x-var-loc (fresh-loc))
      (define x-var `(var ,x null ,(set) ,x-var-loc))
      (define e-env (hash-set env x x-var))
      
      (set! global-store (store-set-var-flags global-store x-var-loc (set)))

      `(lambda (,x-var) ,(init-extra-data e e-env))]

    [`(,e1 ,e2)
     `(call ,(recur e1) ,(recur e2))]
    
    [(? symbol? x) #:when (set-member? (set 'add1 'zero?) x)
     `(primref ,x)]

    [(? symbol? x)
     `(ref ,(hash-ref env x))]))

;; Remove extra data from the AST.
(define (remove-extra-data expr)
  (match expr
    [`(const ,c) c]

    [`(seq ,e1 ,e2)
     `(seq ,(remove-extra-data e1) ,(remove-extra-data e2))]

    [`(if ,g ,e1 ,e2)
     `(if ,(remove-extra-data g) ,(remove-extra-data e1) ,(remove-extra-data e2))]

    [`(lambda (,x-var) ,e)
      (match-define `(var ,x ,_ ,s ,loc-x) x-var)
      `(lambda (,x) ,(remove-extra-data e))]

    [`(call ,e1 ,e2)
     `(,(remove-extra-data e1) ,(remove-extra-data e2))]

    [`(primref ,p)
     p]

    [`(ref ,x-var)
     (match-define `(var ,x ,op ,s ,loc-x) x-var)
     x]))
