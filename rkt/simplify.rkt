#lang racket

(require "utils.rkt")
(require "langs.rkt")

(provide alphatize-mod
         limit-def-params-in-mod
         anf-convert-mod
         cps-convert-mod
         lower-mod
         (contract-out
          [alphatize (-> sm-core-ir? sm-core-ir?)]
          [anf-convert (-> sm-core-ir? sm-core-ir?)]))


(define global-names 0) ;; (set)
(define reserved-bl-x (set '|!|))

(define (alphatize ast) 

  ;; Alphatize let or def body
  (define (alphatize+ ast [env (hash)])
    (define (recur ast) (alphatize+ ast env))
    (define (resolve-id x)
       (define x+ (escape-id-for-C (hash-ref env x (lambda () x))))
       (if (eq? x+ '_u_0003d) 'v_equal x+))
    
    (define (T-bl ast)
      (match ast
        ;; Refs that are not reserved-bl-x
        [`(const ,_) ast]
        [`(ref ,x) #:when (set-member? reserved-bl-x x) ast]
        [`(ref ,x)
        (define x+ (resolve-id x))
        (when (not (hash-has-key? env x))
          (set! global-names (set-add global-names x+)))
        `(ref ,x+)]
        ;; Untagged application
        [`(,fx ,es ...) `(,fx ,@(map T-bl es))]
        ;; Otherwise leave it alone
        [_ ast]))
    
    (match ast
      ;; Update reference
      [`(ref ,x)
       (define x+ (resolve-id x))
       (when (not (hash-has-key? env x))
        (set! global-names (set-add global-names x+)))
       `(ref ,x+)]

      ;; No change to constants, blessed
      [`(const ,_) ast]
      [`(bless ,e0) `(bless ,(T-bl e0))]

      ;; Simple recursion
      [`(if ,g ,t ,e) `(if ,(recur g) ,(recur t) ,(recur e))]

      [`(continue-dispatch ,es ...)
       `(continue-dispatch ,@(map recur es))]

      [`(fail)
       `(fail)]

      [`(fail_to ,fail-ref)
       `(fail_to ,(recur fail-ref))]

      [`(,ell ,e0) #:when (eq? ell '|...|)
       `(,ell ,(recur e0))]
      
      [`(,(and ctor (or 'object 'subword)) ,es ...)
       `(,ctor ,@(map recur es))]

      ;; Remove pointless lets
      [`(let (ref ,x) (ref ,y) ,body)
       (alphatize+ body (hash-set env x (hash-ref env y (lambda () y))))]

      ;; Let
      [`(let (ref ,x) ,rhs ,body)
       (define x+ (gensymb x))
       `(let (ref ,(escape-id-for-C x+)) ,(recur rhs)
             ,(alphatize+ body (hash-set env x x+)))]

      ;; slices
      [`(|[]| ,es ...)
       `(|[]| ,@(map recur es))]
      
      ;; Inner defs
      [`(def ((ref ,fx) ,args ...) ,maybe-fail-to ... ,body ,more)
        (alphatize-inner-def ast env)]

      ;; Untagged application
      [`((ref ,fx) ,es ...) (map recur ast)]

      [_ (pretty-print ast)
        (error 'alphatize-error)]))
  
  ;; Expr -> (ValuesOf (ListOf Expr) Expr)
  (define (get-sibling-inner-defs def-ast)
    (match def-ast
      [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body ,more)
        (define-values (defs rest) (get-sibling-inner-defs more))

        (values
          (append
            (list `(def ((ref ,fx) ,@params) ,@maybe-fail-to ,body))
            defs)
          rest)]
      
      [_ 
        (values
          '()
          def-ast)]))

  ;; Expr (HashOf Symbol Symbol) -> Expr
  (define (alphatize-inner-def def-ast env)
    ;; Unnest the nested sibling defs
    (define-values (defs rest-ast) (get-sibling-inner-defs def-ast))

    ;; Construct an env with all the sibling defs' new names
    (define-values (new-defs env+)
      (for/fold ([new-defs (list)]
                 [env+ env])
                ([def (reverse defs)])
        (match def
          [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body)
            (define fx+ (gensymb fx))
            (define env++ (hash-set env+ fx fx+))
            
            (values
              (cons
                `(def ((ref ,(escape-id-for-C fx+)) ,@params) ,@maybe-fail-to
                  ,body)
                new-defs)
              env++)])))
    
    ;; Alphatize each defs body with env+
    (define final-defs
      (for/list ([def new-defs])
        (match def
          [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body)
            ;; Construct an env for the body
            (define-values (body-env params+)
              (for/fold ([body-env env+]
                         [params+ (list)])
                        ([param (in-list params)])
                (match param
                  [`(ref ,x)
                    (define x+ (gensymb x))
                    (values
                      (hash-set body-env x x+)
                      (append params+ (list `(ref ,(escape-id-for-C x+)))))]
                  [`(,ell (ref ,x)) #:when (eq? ell '|...|)
                    (define x+ (gensymb x))
                    (values
                      (hash-set body-env x x+)
                      (append params+ (list `(,ell (ref ,(escape-id-for-C x+))))))])))
            
            (define alphatized-maybe-fail-to
              (if (null? maybe-fail-to)
                   '()
                   (list (alphatize+ (car maybe-fail-to) env+))))

            `(def ((ref ,fx) ,@params+) ,@alphatized-maybe-fail-to
              ,(alphatize+ body body-env))])))

    ;; Splices/nests the defs back together with `rest-ast` at the center
    (for/fold ([inner-ast (alphatize+ rest-ast env+)])
              ([def (reverse final-defs)])
      (match def
        [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body)
          `(def ((ref ,fx) ,@params) ,@maybe-fail-to ,body ,inner-ast)])))

  (match ast
    [`(let ,lhs ,rhs)
     `(let ,(alphatize+ lhs) ,(alphatize+ rhs))]

    ;; Alphatize defs (w/ param alpha-renaming)
    [`(def ((ref ,fx) ,args ...) ,maybe-fail-to ... ,body)
     ;; TODO: refactor to use the same code as the inner def case
     (define env (hash))
     (define args+
       (for/list ([arg (in-list args)])
         (match arg
           [`(ref ,x)
            (define x+ (gensymb x))
            (set! env (hash-set env x x+))
            `(ref ,(escape-id-for-C x+))]
           [`(,ell (ref ,x)) #:when (eq? ell '|...|)
            (define x+ (gensymb x))
            (set! env (hash-set env x x+))
            `(,ell (ref ,(escape-id-for-C x+)))])))

     (define alphatized-maybe-fail-to
             (if (null? maybe-fail-to)
                  '()
                  (list (alphatize+ (car maybe-fail-to)))))
     
     `(def ((ref ,(escape-id-for-C fx)) ,@args+) ,@alphatized-maybe-fail-to
        ,(alphatize+ body env))]

    [_ (pretty-print ast)
       (error 'alphatize)]))


(define (with-debug-print val-ast ast)
  `(let (ref ,(gensymb '_))
        ((ref _debug__print) (ref _none) (bless (const 1)) ((ref _write) (ref _none) (bless (const 1)) ,val-ast))
        ,ast))

(define (with-print-value val-ast ast)
  `(let (ref ,(gensymb '_))
        (bless ((ref print_debug_value) ,val-ast))
        ,ast))

(define (with-print-values val-asts ast)
  (foldr (lambda (val-ast acc)
            (with-print-value val-ast acc))
         ast
         val-asts))

;; Expr -> Expr
;; A pass that limits the number of arguments a function takes.
(define (limit-def-params ast)
  (define noarg-x '_u__noarg)
  (define standard-arg-count (- bless-arg-count 3)) ;; Number of blessed args not including the overflow slice or fallback or arg-count
  
  (match-define `(def ((ref ,fname) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body) ast)

  (define maybe-fail-x
    (if (null? maybe-fail-to)
      #f
      (match maybe-fail-to
        [`((fail_to (ref ,fail-x)))
          fail-x])))

  ;; (ListOf Expr) Int (or Symbol #f) -> (ValuesOf (ListOf Symbol) Lambda)
  ;; Processes def param list to cap the number of params.
  ;; `ps` is the parameter list. `idx` is the current parameter index.
  ;; `overflow-x` is the name of the overflow splice (once it is needed).
  (define (process-params ps idx overflow-x)
    (match ps
      ['()
        (values (list)
                (lambda (b) b))]
      
      ;; ellipsis case
      [(cons `(,ell ,px) rest-ps) #:when (eq? ell '|...|)
        (unless (null? rest-ps)
          (error 'limit-def-params "Vararg splice (...) must be the final parameter in a definition."))
        (cond
          ;; Slice needs to be gathered
          [(< idx standard-arg-count)
            (let* ([remaining (- standard-arg-count idx)] ; the remaining args before things should be put into the overflow slice
                   [gather-vars (for/list ([i (in-range remaining)]) (gensymb 'gather))]
                   [gather-refs (map (lambda (v) `(ref ,v)) gather-vars)]
                   [slice-var (gensymb 'gather_slice)]
                   [pad-noargs (for/list ([i (in-range (- standard-arg-count remaining))]) `(ref ,noarg-x))])
              (values `(,@gather-refs (ref ,slice-var))
                      (lambda (b)
                        `(let ,px 
                              ((ref _u__gather) (ref _none)
                                                (bless (const ,(+ standard-arg-count 1))) ; +1 for slice-var argument
                                                ,@gather-refs ,@pad-noargs (|[]| (ref ,slice-var))) ; gathers the gather-refs and slice-var into a single slice
                            ,b))))]
          
          ;; Everything is in the overflow slice, so just bind it to the correct name: px
          [else
            (define over-x (if overflow-x
                               overflow-x
                               (gensymb 'overflow)))
            
            (values (if overflow-x '() (list `(ref ,over-x)))
                    (lambda (b)
                      `(let ,px (if (bless ((ref equal) (ref ,noarg-x) (ref ,over-x)))
                                    (ref _empty)
                                    (ref ,over-x))
                          ,b)))])]

      [(cons px rest-ps)
        (cond
          [(< idx standard-arg-count)
            (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) #f)])
              (values (cons px rest-px)
                      (lambda (b)
                        (binder b))))]

          ;; This param will be the overflow list
          [(= idx standard-arg-count)
            (let* ([slice-x (gensymb 'overflow)]
                   [slice-ref `(ref ,slice-x)]
                   [next-slice-x (gensymb 'overflow_rest)])
              (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) next-slice-x)])
                (values (cons slice-ref rest-px)
                        (lambda (b)
                          `(let ,px
                                (if (bless ((ref equal) (ref ,noarg-x) ,slice-ref)) ;; Check overflow arg exists
                                    (ref ,noarg-x)
                                    (if (bless ((ref equal) (ref _empty) ,slice-ref)) ;; Check not empty
                                        (ref ,noarg-x)
                                        ((ref _first) (ref _none) (bless (const 1)) ,slice-ref)))
                              (let (ref ,next-slice-x)
                                   (if (bless ((ref equal) (ref ,noarg-x) ,slice-ref)) ;; Check overflow arg exists
                                       (ref _empty)
                                       (if (bless ((ref equal) (ref _empty) ,slice-ref)) ;; Check not empty
                                           (ref _empty)
                                           ((ref _rest) (ref _none) (bless (const 1)) ,slice-ref)))
                                ,(binder b)))))))]

          ;; Rest of the params to put into the overflow list
          [else
            (let ([next-slice-x (gensymb 'overflow_rest)])
              (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) next-slice-x)])
                (values rest-px 
                        (lambda (b)
                          `(let ,px
                                (if (bless ((ref equal) (ref _empty) (ref ,overflow-x))) ;; Check not empty
                                    (ref ,noarg-x)
                                    ((ref _first) (ref _none) (bless (const 1)) (ref ,overflow-x)))
                              (let (ref ,next-slice-x)
                                   (if (bless ((ref equal) (ref _empty) (ref ,overflow-x))) ;; Check not empty
                                       (ref _empty)
                                       ((ref _rest) (ref _none) (bless (const 1)) (ref ,overflow-x)))
                                ,(binder b)))))))])]))

  ;; Expr (ListOf `(ref ,Symbol)) -> Expr
  ;; Translate call sites to only take a fixed number of arguments and
  ;; translate `(fail ,fail-ref) expressions to `(,fail-ref ,@all-sig-params).
  (define (translate-call-sites ast all-sig-params)
    (define (recur ast) (translate-call-sites ast all-sig-params))

    (match ast
      [`(ref ,x) ast]
      [`(const ,v) ast]
      [`(bless ,e0) ast]

      [`(,ell ,e) #:when (eq? ell '|...|)
       `(,ell ,(recur e))]

      [`(,(and ctor (or 'object 'subword '|[]|)) ,eas ...)
        `(,ctor ,@(map recur eas))]

      [`(let ,x ,e0 ,e1)
       `(let ,x ,(recur e0) ,(recur e1))]

      [`(if ,e0 ,e1 ,e2)
       `(if ,(recur e0) ,(recur e1) ,(recur e2))]

      [`(continue-dispatch ,eas ...)
       `(continue-dispatch ,@(map recur eas))]

      [`(fail)
       (when (not maybe-fail-x)
         (error 'limit-def-params "Fail expressions (fail) must be inside an enclosing def with a (fail_to (ref failx)) annotation."))

       `((ref ,maybe-fail-x) ,@all-sig-params)]

      [`(closures ,bindings ,body)
        `(closures ,bindings ,(recur body))]

      [`(,ef ,eas ...)
       (define eas+ (map recur eas))
       (define ef+ (recur ef))

       (cond
        [(or (equal? ef+ '(ref _raw__apply)) (equal? ef+ '(ref _raw__apply__with__fallback))) ; Special cases that don't gather the tail into a slice
          `(,ef+ ,@eas+)]
        [(<= (length eas+) (- bless-arg-count 1))
          `(,ef+ ,@eas+)]
        [else ;; Overflow: gather tail into a slice
              (define head (take eas+ (- bless-arg-count 1)))
              (define tail (drop eas+ (- bless-arg-count 1)))
              (define residual-slice `(|[]| ,@tail))
              `(,ef+ ,@head ,residual-slice)])]

      [_
        (displayln ast)
        (error 'translate-call-sites-error)]))

  (define-values (new-sig-params body-binder) (process-params params 0 #f))

  ;; Pad the params
  (define extra-params (pad-params (+ (length new-sig-params) 2))) ;; +2 to account for the fallback and arg-count
  (define all-sig-params (append (list `(ref ,fallback-x) `(ref ,arg-count-x)) new-sig-params extra-params))

  `(def ((ref ,fname) ,@all-sig-params)
    ,(body-binder (translate-call-sites body all-sig-params))))




;; Normalizes sub-expressions so they are let bound
;; Normalizes some simple forms into blessed code and junctures with blessed code
(define (anf-convert ast)
  
  ;; Expr -> Expr
  (define (normalize-term ast)
    (normalize ast (λ (x) x)))

  ;; Expr Lambda -> Expr
  (define (normalize ast k)
    (match ast
      [`(ref ,x) (k `(ref ,x))]
      
      [`(const ,v) (k `(const ,v))]

      [`(,ell ,e) #:when (eq? ell '|...|) (k `(,ell ,e))]
      
      [`(bless ,e0)
       (define gx (gensymb 'bl))
       `(let (ref ,gx) ,ast ,(k `(ref ,gx)))]

      [`(,(and ctor (or 'object 'subword '|[]|)) ,eas ...)
       (normalize-names eas
                        (λ (xs)
			  (define t (gensymb 'rv))
                          `(let (ref ,t) (,ctor ,@xs)
				,(k `(ref ,t)))))]

      [`(let ,x ,e0 ,e1)
       (match e0 ;; When the cont is small enough, duplicate it freely
        [`(if ,g ,t ,e) #:when (small-expr? e1)
          (normalize `(if ,g (let ,x ,t ,e1) (let ,x ,e, e1)) k)]
        [_ (normalize e0
                  (λ (e0+)
                    `(let ,x ,e0+
                          ,(normalize e1 k))))])]

      [`(if ,e0 ,e1 ,e2)
       (normalize-name e0
                       (λ (x)
                         (k `(if ,x
                                 ,(normalize-term e1)
                                 ,(normalize-term e2)))))]

      [`(continue-dispatch ,eas ...)
       (normalize-names eas
                        (λ (xs)
                          (k `(continue-dispatch ,@xs))))]

      [`(closures (,bindings ...) ,body) ;; Keep these bindings as they are
        (k 
          `(closures (,@bindings)
              ,(normalize-term body)))]

      [`(,eas ...)
       (normalize-names eas
                        (λ (xs)
                          (k `(,@xs))))]

      [_ (error 'normalize-err)]))

  ;; Expr Lambda -> Expr
  ;; Normalizes the expression to a name which
  ;; is passed to the kont lambda specifying what to do next.
  (define (normalize-name e0 k)
    (match e0
      [`(,_ ...)
       (normalize e0
                  (λ (e0+)
                    (match e0+
                      [`(ref ,_) (k e0+)]
                      [`(const ,_) (k e0+)]
		                  [`(,ell (ref ,_)) #:when (eq? ell '|...|) (k e0+)]
                      [_
                        (let ([tx `(ref ,(gensymb 't))])
                           `(let ,tx ,e0+ ,(k tx)))])))]))

  ;; (ListOf Expr) Lambda -> Expr
  ;; Normalizes the expressions to a list of names
  ;; which is passed to the kont lambda specifying what to do next.
  (define (normalize-names es k)
    (if (null? es)
        (k '())
        (normalize-name (car es)
                        (λ (tx)
                          (normalize-names (cdr es)
                                           (λ (txs)
                                             (k `(,tx ,@txs))))))))

  (match ast
    [`(def ,param ,body)
     `(def ,param ,(normalize-term body))]
    
    [`(let ,name ,rhs)
     `(let ,name ,(normalize-term rhs))]

    [_ (error 'anf-convert-err)]))




(define (cps-convert ast)
  ;; Blessed compilation below adds stack push/pop
  ;;   this code compiles to use these to push
  ;;   a closure for each cont: freevars + fptr

  (define lifted-defs '())
  (define (lift-def! def) (set! lifted-defs (cons def lifted-defs)))
  
  (define (all-local-work? ast)
    (match ast ;; does this ast compile without nonlocal jumps?
      [`(,(or 'bless 'const 'ref 'object 'subword) ,_ ...) #t]
      [`((ref ,fx) ,_ ...) (set-member? reserved-bl-x fx)]
      [`(if ,es ...) (andmap all-local-work? es)]
      [`(let ,_ ,e0 ,e1)
       (and (all-local-work? e0) (all-local-work? e1))]
      [_ #f]))
  
  (define (T-cps ast defname)
    (define (recur ast) (T-cps ast defname))

    (define (free ast)
      (define (freevars ast)
        (define (freebless ast)
          (match ast
            [`(ref ,x) (set x)]
            [`(,fe ,aes ...) ;; do not count fun-expr
              (foldl set-union (set) (map freevars aes))]
            [_ (set)]))
        
        (match ast
          [`(ref ,x) (set x)]
          [`(bless ,e0) (freebless e0)]
          [`(let ,lhs ,rhs ,body)
            (set-union (freevars rhs)
                       (set-subtract (freevars body) (freevars lhs)))]
          [`(,es ...)
            (foldl set-union (set) (map freevars es))]
          [_ (set)]))
      
      (set-subtract (freevars ast) global-names reserved-bl-x
		    (set 'unbox_subword 'get_subword_tag)))

    (define (lift-cont! x body type rhs)
      (define freelst (set->list (set-remove (free body) x)))
      (define kname (gensymb (sym-append defname type)))

      (lift-def! ;; assumes def interface w/ dummy fallback
       `(def ((ref ,kname) (ref ,(gensymb '_)) (ref ,(gensymb '_)) (ref ,x))
          ,(foldl
            (lambda (free-x body+)
              `(let (ref ,free-x) (bless ((ref stack_pop)))
              ,body+))
            (recur body)
            freelst)))

      (foldr
        (lambda (free-x body+)
	       `(let (ref ,(gensymb '_))
               (bless ((ref stack_push) (ref ,free-x)))
               ,body+))
        `(let (ref ,(gensymb '_))
              (bless ((ref stack_push) ((ref blessed_t) (ref ,kname))))
              ,rhs)
        freelst))
    
    (match ast
      [(or `(ref ,_) `(const ,_)) `(return ,ast)]
      
      [`(let (ref ,x) ,(and atom (or `(ref ,_) `(const ,_))) ,body)
       `(let (ref ,x) ,atom
	     ,(recur body))]

      [`(let (ref ,x) (bless ,rhs) ,body)
       `(let (ref ,x) (bless ,rhs)
	     ,(recur body))]

      [`(let (ref ,x) (,(and ctor (or 'object 'subword '|[]|)) ,xs ...) ,body)
       `(let (ref ,x) (,ctor ,@xs)
	     ,(recur body))]
      
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       #:when (all-local-work? `(if ,g ,t ,e))
       `(let (ref ,x) (if ,g ,(recur t) ,(recur e)) ,(recur body))]
      
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       (lift-cont! x body "ifkont" `(if ,g ,(recur t) ,(recur e)))]
      
      [`(let (ref ,x) (,fx ,args ...) ,body)
       (lift-cont! x body "appkont" `(,fx ,@args))]

      [`(if ,guard ,then ,else) 
       `(if ,guard ,(recur then) ,(recur else))]
      
      [`(continue-dispatch ,_ ...) ast] 

      [`(closures (,bindings ...) ,body)
        `(closures (,@bindings)
          ,(recur body))]

      [`((ref ,fx) ,args ...)
       `((ref ,fx) ,@args)]

      [_ (pretty-print ast)
	 (error 'T-cps-err)]))

  (match ast
    [`(def ((ref ,fx) ,param ...) ,body)
     (define body+ (T-cps body fx))
     `((def ((ref ,fx) ,@param) ,body+) ,@lifted-defs)]

    [`(let ,lhs ,(and rhs (or `(const ,_) `(object ,_ ...))))
     `(let ,lhs ,rhs)]
    
    [`(let ,lhs ,rhs)
     (error 'let-cps-not-fully-supported)]

    [_ (pretty-print ast) (error 'cps-convert-err)]))


(define (alphatize-mod mod)
  (set! global-names (set 'v_equal
                          '_u_0003d)) ; Unicode name for =
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (set! reserved-bl-x
      (set-union reserved-bl-x
        (for/set ([(ast) (in-list inline)])
          (match ast [`(blessed ((ref ,fx) . ,_) ,_) fx]))))

     (define defs+
        (for/list ([ast defs]) 
          (alphatize ast)))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,(for/list ([ast lets]) (alphatize ast))
	      ,defs+
	      ,methods ,types)]))

(define (limit-def-params-in-mod mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
        (for/list ([ast defs]) 
          (limit-def-params ast)))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets
	      ,defs+
	      ,methods ,types)]))

(define (anf-convert-mod mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
        (for/list ([ast defs]) 
          (anf-convert ast)))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,(for/list ([ast lets]) (anf-convert ast))
	      ,defs+
	      ,methods ,types)]))

(define (cps-convert-mod mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
       (foldr append '() ;; flatten (CPS may emit >1 def for each def)
	      (for/list ([ast defs]) 
          (cps-convert ast))))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets
	      ,defs+
	      ,methods ,types)]))

(define (lower-mod mod)
  (define (lower-stmt ast [return-var #f]) 
    (define (recur ast) (lower-stmt ast return-var))

    ;; Flattens CPS code into basic-blocks of blessed 
    (match ast

      ;; Assignment to fresh immutable var
      [`(let (ref ,x) (bless ,rhs) ,body)
       `(((ref =) (ref ,x) ,rhs)
	       ,@(recur body))]

      ;; Let bound const or ref
      [`(let (ref ,x) ,(and rhs (or `(const ,_) `(ref ,_))) ,body)
       `(((ref =) (ref ,x) ,rhs)
	       ,@(recur body))]

      ;; Let bound subword
      [`(let (ref ,x) (subword (ref ,tag) ,e0) ,body)
       `(((ref =) (ref ,x)
	                ((ref box_subword) ((ref unbox_subword) ,e0) (ref ,tag)))
	       ,@(recur body))]

      ;; Let bound object
      [`(let (ref ,x) (object (ref ,tag) ,es ...) ,body)
       (define rx (gensymb 'a))
       `(((ref =) ((ref |!|) (ref ,rx))
	                ((ref alloc) (const ,(+ 1 (length es)))))
	       (do ((ref init_obj) (ref ,rx) (const 0)
                             ((ref obj_head_word)
                              (const ,(length es))
                              (ref ,(sym-append tag "_vtable")))))
	       ,@(map (lambda (ae i)
		              `(do ((ref init_obj) (ref ,rx) (const ,i) ,ae)))
		            es
		            (range 1 (add1 (length es))))
	       ((ref =) (ref ,x) ((ref u64bit_or) ((ref freeze) (ref ,rx)) (const 1)))
	       ,@(recur body))]

      ;; Lower List/Slice Literals
      [`(let (ref ,x) (|[]| ,es ...) ,body)
       (define (make-chunk-ast target-x elems)
         (define rx (gensymb 'sl_chk))
         ;; Alloc len + 1 for header-zero at front
         `(((ref =) ((ref |!|) (ref ,rx)) ((ref alloc) (const ,(+ 1 (length elems)))))
           ;; Set the header at index 0 to 0 (NULL/None)
           (do ((ref init_obj) (ref ,rx) (const 0) (const 0)))
           ;; Fill elements starting at index 1
           ,@(for/list ([e elems] [i (in-naturals)])
               `(do ((ref init_obj) (ref ,rx) (const ,(+ 1 i)) ,e)))
           ((ref =) (ref ,target-x) ;; final value is (rx + 1) | 2
            ((ref u64bit_or)
	     ((ref plus) ((ref manys_t) ((ref freeze) (ref ,rx))) (const 1))
	     (const 2)))))

       (define (join-chunks ops)
         (match ops
           ['() `(((ref =) (ref ,x) (ref _empty)))] 
           [`((,_ ... ((ref =) (ref ,last-v) ,_)))
	    (append (first ops) `(((ref =) (ref ,x) (ref ,last-v))))]
           [`(,c1 ,c2 ,rest ...)
            (match-let ([`(,_ ... ((ref =) (ref ,v1) ,_)) c1]
                        [`(,_ ... ((ref =) (ref ,v2) ,_)) c2])
              (join-chunks (cons (append c1 c2 
					 `(((ref =) (ref ,(gensymb 'join)) 
					    ((ref +) (ref none) (bless (const 2)) (ref ,v1) (ref ,v2)))))
				 rest)))]))

       (define-values (all-chunks last-chunk)
         (for/fold ([chunks '()] [curr-chunk '()]) ([e (in-list es)])
           (match e
             [`(,ell ,v) #:when (eq? ell '|...|) 
              (define chunk-ops
                (if (null? curr-chunk)
		    '()
                    (let ([tv (gensymb 'chk)])
                      (list (make-chunk-ast tv (reverse curr-chunk))))))
              (define splice-op 
                (let ([tv (gensymb 'spl)])
                  `(((ref =) (ref ,tv) ,v))))
              
              (values (append chunks chunk-ops (list splice-op)) '())]
             
             [_ (values chunks (cons e curr-chunk))])))

       (define final-chunks 
         (if (null? last-chunk) 
             all-chunks
             (let ([tv (gensymb 'last)])
               (append all-chunks (list (make-chunk-ast tv (reverse last-chunk)))))))
       
       (append (join-chunks final-chunks)
               (recur body))]

      ;; If is just if, but we start new basic blocks
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       (define x+ (gensymb x)) ;; lower in-place with x+ as mut join var
       `(,@(lower-stmt `(if ,g ,t ,e) x+)
         ((ref =) (ref ,x) ((ref freeze) (ref ,x+)))
         ,@(recur body))]
      
      [`(if ,g ,t ,e)
       (define g+ (gensymb 'grd))
       `(((ref =) (ref ,g+) ((ref eq) ,g (ref _false)))
	       (if (ref ,g+) ((ref |{}|) ,@(recur e)) ((ref |{}|) ,@(recur t))))]
      
      ;; Invoke fun-ptr at fallback ptr, then increment and pass fwd
      [`(continue-dispatch ,fallback ,args ...)
       ;; There will be 7 args at this point with the last one being a slice
       (define fun (gensymb 'fallbackfun))
       (define fb1 (gensymb 'fallbk1_))
       (define rv (gensymb 'rv))
       `(((ref =) (ref ,fun) ((ref deref) ((ref anys_t) ,fallback))) 
         ((ref =) (ref ,fb1) ((ref plus) ((ref manys_t) ,fallback) (const 1)))
         (return ((ref ,fun) (ref ,fb1) ,@args)))]

      ;; Construct closures
      [`(closures (((ref ,xs) ,(and objs `(object ,_ ...))) ...) ,body)
      
        (define-values (alloc-objects-code renamings)
          (for/fold ([alloc-objects-code (list)]
                     [renamings (hash)])
                    ([x (reverse xs)]
                     [obj (reverse objs)])
            (match obj
              [`(object (ref ,tag) ,fvs ...)
                (define rx (gensymb x))

                (values
                  (cons
                    `((ref =) ((ref |!|) (ref ,rx))
                              ((ref alloc) (const ,(+ 1 (length fvs)))))
                    alloc-objects-code)
                  
                  (hash-set renamings x rx))])))
       
       (define (rename-x x)
        (hash-ref renamings x x))
       (define (rename-ref ref)
        (match ref
          [`(ref ,x)
           (if (hash-has-key? renamings x)
               ;; x must be a closure: rename, freeze, and tag
               ;; TODO: do we need to freeze here?
               `((ref u64bit_or) ((ref freeze) (ref ,(rename-x x))) (const 1))
               `(ref ,x))]))
      
       (define init-objects-code
        (foldr append '() ;; flatten one level
          (for/list ([x xs]
                    [obj objs])
            (match obj
              [`(object (ref ,tag) ,fvs ...)
                (define rx (rename-x x))
                (define r-fvs (map rename-ref fvs))

                ;; Head word + fvs
                `((do ((ref init_obj) (ref ,rx) (const 0)
                                      ((ref obj_head_word)
                                      (const ,(length r-fvs))
                                      (ref ,(sym-append tag "_vtable")))))
                  
                  ,@(map (lambda (fv i)
                          `(do ((ref init_obj) (ref ,rx) (const ,i) ,fv)))
                        r-fvs
                        (range 1 (add1 (length r-fvs)))))]))))

       (define freeze-objects-code
        (for/list ([x xs]
                   [obj objs])
          (define rx (rename-x x))
          `((ref =) (ref ,x) ((ref u64bit_or) ((ref freeze) (ref ,rx)) (const 1)))))

       `(,@alloc-objects-code
         ,@init-objects-code
         ,@freeze-objects-code

         ,@(recur body))]

      ;; Return to current continuation
      [`(return ,ae) #:when return-var ;; local var cont
       `(((ref =) ((ref |!|) (ref ,return-var)) ,ae))]
      [`(return ,ae)
       (define kfun (gensymb 'kfun)) ;; nonlocal stack cont
       `(((ref =) (ref ,kfun) ((ref stack_pop)))
	        (return ((ref ,kfun) (const 0) (const 1) ,ae)))] ;; Q: why calling with (const 0) instead of (ref none)?
      
      ;; Emit a method call based on the _pos and _link variables
      [`((ref ,fx)) (error "Not yet supported: thunk call, no args")]
      [`((ref ,fx) ,arg0 ,args ...)
       `((return ((ref ,fx) ,arg0 ,@args)))]
      
      [_
       (pretty-print ast)
	     (error "lower-ast: Unknown AST")]))
  
  (define (def->blessed ast)
    (match ast
      [`(def ((ref ,fx) ,args ...) ,body)
        `(blessed ((ref ,fx) ,@args) ((ref |{}|) ,@(lower-stmt body)))]))

  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     ;; Use helpers just above to lower these defs to blessed code
     `(module ,name ,mtag ,bless ,inline ,(append (map def->blessed defs) blessed)
	      ,lets
	      ,defs
	      ,methods ,types)]))