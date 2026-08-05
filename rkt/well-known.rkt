#lang racket

(require "utils.rkt"
         "simplify.rkt"
         "helpers.rkt")

(provide lift-well-known-defs)


;; AlphatizedModule -> WellKnownModule
(define (lift-well-known-defs mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
       (foldr append '() ;; flatten one level
        (for/list ([ast defs]) 
          (set->list (lift-well-known/def ast)))))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs+ ,methods ,types)]))

;; Expr -> (SetOf Expr)
(define (lift-well-known/def def-ast)
  (match def-ast
    [`(def (,xs ...) ,maybe-fail-to ... ,body)
      (define-values (new-body new-defs) (lift-well-known/ast body))
      (set-add new-defs `(def (,@xs) ,@maybe-fail-to ,new-body))]
    [_ (error 'lift-well-known-defs)]))

;; Expr -> (ValuesOf Expr (SetOf Expr))
;; Returns the modified expression and a list of top-level defs which are being lifted out.
(define (lift-well-known/ast ast)
  (define (recur ast outer-expr)
    (define-values (expr defs) (lift-well-known/ast ast))
    (values
      (outer-expr expr)
      defs))

  (define (recur-exprs asts outer-expr)
    (define-values (exprs defs)
      (for/foldr ([exprs (list)]
                  [defs (set)])
                ([ast asts])
        (define-values (expr new-defs) (lift-well-known/ast ast))
        
        (values
          (cons expr exprs)
          (set-union defs new-defs))))

    (values
      (outer-expr exprs)
      defs))

  (match ast
    [`(ref ,x)
      (values `(ref ,x) (set))]

    ;; No change to constants
    [`(const ,_) (values ast (set))]
    
    ;; Bless
    [`(bless ,e0)
      (values ast (set))]

    ;; Simple recursion
    [`(if ,g ,t ,e)
      (define-values (g-expr g-defs) (lift-well-known/ast g))
      (define-values (e-expr e-defs) (lift-well-known/ast t))
      (define-values (t-expr t-defs) (lift-well-known/ast e))

      (values
        `(if ,g-expr ,e-expr ,t-expr)
        (set-union g-defs e-defs t-defs))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es
                   (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail)
     (values `(fail) (set))]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (define-values (expr defs) (lift-well-known/ast e0))

      (values
        `(,ell ,expr)
        defs)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-exprs es
                   (lambda (es) `(,ctor ,@es)))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (define-values (rhs-expr rhs-defs) (lift-well-known/ast rhs))
      (define-values (body-expr body-defs) (lift-well-known/ast body))

      (values
        `(let (ref ,x) ,rhs-expr
              ,body-expr)
        (set-union rhs-defs body-defs))]

    ;; Slices
    [`(|[]| ,es ...)
      (recur-exprs es
                   (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def ((ref ,fx) ,xs ...) ,maybe-fail-to ... ,body ,more)
      (lift-well-known/inner-def ast)]

    ;; Untagged application
    [`((ref ,fx) ,fallback ,arg-count ,es ...)
      (define-values (fx-expr fx-defs) (lift-well-known/ast `(ref ,fx)))
      (define-values (_f-expr _f-defs) (lift-well-known/ast fallback))
      (define-values (new-es es-defs)
        (for/foldr ([new-es (list)]
                    [defs (set)])
                   ([e es])
          (define-values (new-e e-defs) (lift-well-known/ast e))

          (values
            (cons new-e new-es)
            (set-union defs e-defs))))

      (values
        `(,fx-expr ,fallback ,arg-count ,@new-es)
        (set-union fx-defs es-defs))]))


;; Expr -> (ValuesOf Expr (SetOf Expr))
(define (lift-well-known/inner-def def-ast)

  (struct def-group
    [defs        ;; (ListOf Expr)
     free-vars]  ;; (CollectionOf Variable)
    #:transparent)

  ;; (ListOf DefGroup) -> (ListOf Expr)
  (define (flatten-def-groups def-groups)
    (foldl append '()
           (map (lambda (g) (def-group-defs g)) def-groups)))

  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-nested-sibling-defs def-ast))

  (define-values (rest-expr rest-new-defs) (lift-well-known/ast rest-ast))

  ;; We need to extract fail chains in order to know what is the first def in the chain to test if it
  ;; is well-known and, if it is well-known, pass along all free variables for the entire chain.
  (define fail-chains (get-fail-chains defs))

  ;; Find free vars for each fail chain (and construct def groups)
  (define def-groups
    (for/fold ([def-groups (set)]) ;; TODO: refactor to for/set
              ([chain fail-chains])
      (define def-g
        (for/fold ([curr-def-group (def-group (list) (set))])
                  ([def-name chain])

          (define def (get-def-with-name defs def-name))
          
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,(and params (or `(ref ,xs)
                                                                                    `(|...| (ref ,xs)))) ...) ,maybe-fail-to ...
                ,body)

              (define body-free (free-vars body))

              (define xs-to-remove (set-union (set fallback-x arg-count-x) (list->set xs) global-names reserved-bl-x))
              (define def-free-vars
                (set->list
                  (set-subtract body-free xs-to-remove)))

              (define def+
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,@maybe-fail-to ,body))

              (def-group (append (def-group-defs curr-def-group) (list def+))
                         (set-union (list->set def-free-vars) (def-group-free-vars curr-def-group)))])))
      
      (set-add def-groups def-g)))


  ;; Determine whether def groups are well-known
  (define well-known-def-groups
    (for/fold ([well-known-def-groups (set)])
              ([curr-def-group def-groups])
      (define first-def-name (get-def-name (car (def-group-defs curr-def-group))))

      (if (is-well-known-in? first-def-name def-ast)
          (set-add well-known-def-groups curr-def-group)
          well-known-def-groups)))

  (define well-known-def-names
    (get-def-names
      (foldl append '()
            (map (lambda (g) (def-group-defs g)) (set->list well-known-def-groups)))))

  (define non-well-known-def-groups (set-subtract def-groups well-known-def-groups))
  (define non-well-known-defs (flatten-def-groups (set->list non-well-known-def-groups)))

  ;; TODO: for lifting mutually recurive defs, we will need to combine their free variables (before converting the param lists and call sites)

  ;; Lift well-known def groups
  (define lifted-def-groups
    (for/set ([curr-def-group well-known-def-groups])
              
      ;; pick an arbitrary ordering for the free vars
      (define group-free-vars (set->list (set-subtract (def-group-free-vars curr-def-group) well-known-def-names)))
      (define group-free-var-refs (map (lambda (x) `(ref ,x)) group-free-vars))

      (define new-lifted-defs
        (for/set ([def (def-group-defs curr-def-group)])
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body)

              (define new-lifted-def
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@group-free-var-refs ,@params) ,@maybe-fail-to ,body))

              ;; Use unescaped names when registering (they are escaped later on)
              ;; TODO: When first def: register
              ;;(register-method! fx #f new-apply-x)

              new-lifted-def])))

      (def-group (set->list new-lifted-defs) group-free-vars)))


  ;; Pass free variables to well known call sites
  (define-values (lifted-defs non-well-known-defs+ rest-expr+)
    (for*/fold ([defs+ (flatten-def-groups (set->list lifted-def-groups))]
                [non-well-known-defs+ non-well-known-defs]
                [rest-expr+ rest-expr])
               ([lifted-group lifted-def-groups]
                [def (def-group-defs lifted-group)])
      
      (define free-var-refs (map (lambda (x) `(ref ,x)) (def-group-free-vars lifted-group)))
      
      (define (lift-calls e)
        (lift-well-known-call-sites e (get-def-name def) free-var-refs))

      (values
        (map lift-calls defs+)
        (map lift-calls non-well-known-defs+)
        (lift-calls rest-expr+))))

  ;; Lift well-known defs from newly lifted defs bodies
  (define lifted-defs+
    (foldl set-union (set)
      (for/list ([def lifted-defs])
        (match def
          [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body)
            (define-values (new-body new-defs) (lift-well-known/ast body))
            
            (set-add
              new-defs
              `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,@maybe-fail-to ,new-body))]))))

  ;; Lift well-known defs from bodies of non-well-known-defs
  (define-values (lifted-defs++ non-well-known-defs++)
    (for/fold ([lifted-defs++ lifted-defs+]
               [non-well-known-defs++ (list)])
              ([def non-well-known-defs+])
      (match def
        [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body)
          (define-values (new-body new-defs) (lift-well-known/ast body))

          (values
            (set-union new-defs lifted-defs++)
            (append
              non-well-known-defs++
              (list `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,@maybe-fail-to ,new-body))))])))

  ;; Lift well-known defs from rest-expr
  (define-values (rest-expr++ new-defs-from-rest) (lift-well-known/ast rest-expr+))

  (add-to-global-names! well-known-def-names)

  (values
    (nest-sibling-defs non-well-known-defs++ rest-expr++)
    (set-union lifted-defs++ new-defs-from-rest)))

;; Expr -> (SetOf Symbol)
(define (free-vars ast)
  (match ast
    [`(ref ,x)
      (set x)]

    [`(const ,_) (set)]
    
    ;; Bless
    [`(bless ,e0)
      (define (freebless ast)
        (match ast
          [`(ref ,x) (set x)]
          [`((ref ,fx) ,aes ...) ;; do not count fun-expr
            (foldl set-union (set) (map freebless aes))]
          [_ (set)]))

      (freebless e0)]

    [`(if ,g ,t ,e)
      (set-union (free-vars g) (free-vars t) (free-vars e))]

    [`(continue-dispatch ,es ...)
      (foldl set-union (set) (map free-vars es))]
    
    [`(fail) (set)]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (free-vars e0)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (foldl set-union (set) (map free-vars es))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (set-union (free-vars rhs) (set-remove (free-vars body) x))]

    ;; Slices
    [`(|[]| ,es ...)
      (foldl set-union (set) (map free-vars es))]

    ;; Inner def
    [`(def ((or `(ref ,xs) `(|...| (ref ,xs))) ...) ,maybe-fail-to ... ,body ,more)
      (set-subtract
        (set-union (free-vars body) (free-vars more))
        (list->set xs))]

    ;; Untagged application
    [`(,es ...)
      (foldl set-union (set) (map free-vars es))]))

;; Expr Symbol (ListOf Ref) -> Expr
(define (lift-well-known-call-sites ast def-name free-var-refs)
  (define (recur ast)
    (lift-well-known-call-sites ast def-name free-var-refs))

  (match ast
    [`(ref ,x) ast]
    [`(const ,_) ast]
    [`(bless ,e0) ast] ;; TODO: Are call sites allowed inside bless?

    [`(if ,g ,t ,e)
     `(if ,(recur g) ,(recur t) ,(recur e))]

    [`(continue-dispatch ,es ...)
     `(continue-dispatch ,@(map recur es))]
    
    [`(fail) ast]
    [`(fail_to ,_) ast]

    [`(,ell ,e0) #:when (eq? ell '|...|)
     `(,ell ,(recur e0))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
     `(,ctor ,@(map recur es))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
     `(let (ref ,x) ,(recur rhs) ,(recur body))]

    ;; Slices
    [`(|[]| ,es ...)
     `(|[]| ,@(map recur es))]

    ;; Inner/outer defs
    [`(def (,xs ...) ,body ...)
     `(def (,@xs) ,@(map recur body))]

    ;; Well-known call site
    [`((ref ,fx) ,fallback ,arg-count ,es ...)
     #:when (equal? fx def-name)
     `((ref ,fx) ,fallback ,arg-count ,@free-var-refs ,@(map recur es))]
    
    ;; Remaining untagged applications
    [`(,es ...)
     `(,@(map recur es))]))

;; Symbol Expr -> Bool
(define (is-well-known-in? def-name ast)
  (define (recur ast)
    (is-well-known-in? def-name ast))

  (match ast
    [`(ref ,x)
      (not (equal? x def-name))]
    
    [`(const ,_) #t]
    [`(bless ,e0) (recur e0)]

    [`(if ,g ,t ,e)
     (and (recur g) (recur t) (recur e))]

    [`(continue-dispatch ,es ...)
     (andmap recur es)]
    
    [`(fail) #t]
    [`(fail_to ,_) #t]

    [`(,ell ,e0) #:when (eq? ell '|...|)
     (recur e0)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
     (andmap recur es)]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
     (and (recur rhs) (recur body))]

    ;; Slices
    [`(|[]| ,es ...)
     (andmap recur es)]

    ;; Inner/outer defs
    [`(def (,xs ...) ,body ...)
     (andmap recur body)]

    ;; Well-known call site
    [`((ref ,fx) ,es ...)
     #:when (equal? fx def-name)
     (andmap recur es)]
    
    ;; Remaining untagged applications
    [`(,es ...)
     (andmap recur es)]))

(module+ test
  (require rackunit)
  
  (check-equal?
    (is-well-known-in? 'fx
      `(def ((ref gx) (ref fallback) (ref arg_count) (ref arg1))
          ((ref fx) (ref none) (const 1) (ref arg))))
    #t)

  (check-equal?
    (is-well-known-in? 'fx
      `(def ((ref gx) (ref fallback) (ref arg_count) (ref arg1))
          ((ref indirect_call) (ref none) (ref fx))))
    #f)
  
  (define ast1
    `(def ((ref gx) (ref fallback) (ref arg_count) (ref arg1)) (fail_to (ref hx))
          (let (ref x)
               (let (ref y) (const 5)
                  (if (ref true)
                      ((ref indirect_call) (ref none) (ref fx))
                      ((ref fx) ((ref hx) (ref y)))))
            (ref x))))

  (check-equal? (is-well-known-in? 'fx ast1) #f)
  (check-equal? (is-well-known-in? 'gx ast1) #t)
  (check-equal? (is-well-known-in? 'hx ast1) #t)
  (check-equal? (is-well-known-in? 'indirect_call ast1) #t)
  (check-equal? (is-well-known-in? 'y ast1) #f))