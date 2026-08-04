#lang racket

(require "utils.rkt"
         "simplify.rkt"
         "helpers.rkt")

(provide clo-convert-mod)

(define method-map (hash))
(define (register-method! name obj name+)
  (set! method-map (hash-set method-map (cons name obj) name+)))

(define types-st (set))
(define (register-type! tag)
  (set! types-st (set-add types-st tag))
  tag)

(define apply-x '__apply__)
(define escaped-apply-x (escape-id-for-C apply-x))

;; AlphatizedModule -> CloModule
(define (clo-convert-mod mod)
  (set! method-map (hash))
  (set! types-st (set))

  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
       (foldr append '() ;; flatten one level
        (for/list ([ast defs]) 
          (clo-convert ast))))

     ;; Generate __apply__ for function pointers
     (define fun-ptr-x (gensymb 'fun_ptr))
     (define arg-count-x (gensymb 'arg_count))
     (define rest-args-x (gensymb 'args))
     (define apply-fun-ptr-x (gensymb 'apply_fun_ptr))

     ;; so-far is 4 since we already have the fallback, arg count, fun ptr, and overflow splice args
     (define arg-xs (pad-params 4))

     (define apply-fun-ptr-def
      `(def ((ref ,(escape-id-for-C apply-fun-ptr-x)) (ref ,(gensymb 'fallback)) (ref ,arg-count-x) (ref ,fun-ptr-x) ,@arg-xs (... (ref ,rest-args-x)))
        ((ref _apply_on_slice) (ref ,fun-ptr-x) (ref ,arg-count-x) ,@arg-xs (ref ,rest-args-x))))
    
     (register-method! apply-x #f apply-fun-ptr-x)


     (define all-methods (append
                          methods
                          (hash->list method-map)))

     (define all-types (append
                        types
                        (set->list types-st)))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,(cons apply-fun-ptr-def defs+) ,all-methods ,all-types)]))

;; Expr -> (ListOf Expr)
(define (clo-convert def-ast)
  (match def-ast
    [`(def (,xs ...) ,maybe-fail-to ... ,body)
      (define-values (expr new-defs _) (clo-convert-ast body))
      (append (list `(def (,@xs) ,@maybe-fail-to ,expr)) (set->list new-defs))]
    [_ (error 'clo-convert-defs)]))

;; Expr -> (ValuesOf Expr (SetOf Expr) (SetOf Variable))
;; Returns the modified expression, a list of top-level defs for
;; each inner def's body, and a list of free variables for the expresion.
(define (clo-convert-ast ast)
  (define (recur ast outer-expr)
    (define-values (expr defs free) (clo-convert-ast ast))
    (values
      (outer-expr expr)
      defs
      free))

  (define (recur-exprs asts outer-expr)
    (define-values (exprs defs free)
      (for/foldr ([exprs (list)]
                  [defs (set)]
                  [free (set)])
                ([ast asts])
        (define-values (expr new-defs new-free) (clo-convert-ast ast))
        
        (values
          (cons expr exprs)
          (set-union defs new-defs)
          (set-union free new-free))))

    (values
      (outer-expr exprs)
      defs
      free))

  (match ast
    [`(ref ,x)
      (values `(ref ,x)
              (set)
              (set x))]

    ;; No change to constants
    [`(const ,_) (values ast (set) (set))]
    
    ;; Bless
    [`(bless ,e0)
      (define (freebless ast)
        (match ast
          [`(ref ,x) (set x)]
          [`((ref ,fx) ,aes ...) ;; do not count fun-expr
            (foldl set-union (set) (map freebless aes))]
          [_ (set)]))

      (values
        ast
        (set)
        (freebless e0))]

    ;; Simple recursion
    [`(if ,g ,t ,e)
      (define-values (g-expr g-defs g-free) (clo-convert-ast g))
      (define-values (e-expr e-defs e-free) (clo-convert-ast t))
      (define-values (t-expr t-defs t-free) (clo-convert-ast e))

      (values
        `(if ,g-expr ,e-expr ,t-expr)
        (set-union g-defs e-defs t-defs)
        (set-union g-free e-free t-free))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es
                   (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail)
     (values `(fail) (set) (set))]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (define-values (expr defs free) (clo-convert-ast e0))

      (values
        `(,ell ,expr)
        defs
        free)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-exprs es
                   (lambda (es) `(,ctor ,@es)))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (define-values (rhs-expr rhs-defs rhs-free) (clo-convert-ast rhs))
      (define-values (body-expr body-defs body-free) (clo-convert-ast body))

      (values
        `(let (ref ,x) ,rhs-expr
              ,body-expr)
        (set-union rhs-defs body-defs)
        (set-union rhs-free (set-remove body-free x)))]

    ;; Slices
    [`(|[]| ,es ...)
      (recur-exprs es
                   (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def ((ref ,fx) ,xs ...) ,maybe-fail-to ... ,body ,more)
      (clo-convert-inner-def ast)]

    ;; Untagged application
    [`((ref ,fx) ,fallback ,arg-count ,es ...)
      (define-values (fx-expr fx-defs fx-free) (clo-convert-ast `(ref ,fx)))
      (define-values (_f-expr _f-defs fallback-free) (clo-convert-ast fallback))
      (define-values (new-es es-defs es-free)
        (for/foldr ([new-es (list)]
                    [defs (set)]
                    [free (set)])
                   ([e es])
          (define-values (new-e e-defs e-free) (clo-convert-ast e))

          (values
            (cons new-e new-es)
            (set-union defs e-defs)
            (set-union free e-free))))

      (define app-expr
        (if (set-member? global-names fx)
          ;; In this case, we statically know that fx must be a fun ptr and not a closure
          `(,fx-expr ,fallback ,arg-count ,@new-es)

          ;; The arg count here is for applying fx (so it is only the length of new-es)
          `((ref ,escaped-apply-x) (ref _none) (bless (const ,(length new-es))) ,fx-expr ,@new-es)))

      (values
        app-expr
        (set-union fx-defs es-defs)
        (set-union fx-free fallback-free es-free))]))


;; Expr -> (ValuesOf Expr (SetOf Expr) (SetOf Variable))
(define (clo-convert-inner-def def-ast)
  ;; Some helpers for this function
  (struct def-group
    [defs        ;; (ListOf Expr)
     free-vars]  ;; (SetOf Variable)
    #:transparent)

  (define (is-first-def-in-group? group def)
    (equal? def
            (first (def-group-defs group))))


  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-nested-sibling-defs def-ast))

  (define-values (rest-expr rest-new-defs rest-free) (clo-convert-ast rest-ast))


  ;; A set of lists of def names which are linked together in a fail chain by fail_to.
  ;; The first def in a chain is the entry point.
  ;; (We need to do this in order to know what is the first def in the chain which we want to
  ;; convert to an __apply__ and to create a single closure for the entire chain of defs)
  (define fail-chains
    (for/fold ([chains (set)]) ;; (SetOf (ListOf Symbol))
              ([def defs])
      (match def
        [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body)

          ;; (or Symbol #f)
          (define maybe-fail-x
            (if (null? maybe-fail-to)
              #f
              (match maybe-fail-to
                [`((fail_to (ref ,fail-x)))
                  fail-x])))
          
          (cond
            ;; Add the fail-x to an existing or new chain
            [maybe-fail-x
              (define-values (updated-chains updated)
                (for/fold ([updated-chains (set)]
                           [updated #f])
                          ([chain chains])

                  (if (equal? (last chain) fx)
                      ;; If this def is at the end of the chain then extend the existing chain with fail-x
                      (values
                        (set-add updated-chains (append chain (list maybe-fail-x))) ;; Extend existing chain
                        #t)
                      
                      ;; Otherwise keep looking for the chain to extend
                      (values
                        (set-add updated-chains chain)
                        updated))))
              
              (if updated
                  updated-chains ;; Extended an existing chain
                  (set-add chains (list fx maybe-fail-x)))] ;; Otherwise, start new chain
            
            ;; Either this def's name (i.e. fx) will have already been added to a chain or this def's
            ;; name will be start a new singleton chain
            ;; (this must be the last def in the chain since it doesn't have a fail-to)
            [else
              (define found-in-chain
                (for/first ([chain chains]
                            #:when (equal? (last chain) fx))
                  #t))

              ;; If this def is at the end of the chain then we are done with this chain (so do nothing).
              ;; Otherwise add the def to a new singleton chain.
              (if found-in-chain
                  chains
                  (set-add chains (list fx)))])])))

  ;; Closure convert def bodies and find free vars for each def group
  (define-values (def-groups lifted-defs-from-bodies)
    (for/fold ([def-groups (set)]
               [new-defs (set)])
              ([chain fail-chains])
      (define-values (def-g more-new-defs)
        (for/fold ([curr-def-group (def-group (list) (set))]
                   [new-defs (set)])
                  ([def-name chain])

          (define def (get-def-with-name defs def-name))
          
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,(and params (or `(ref ,xs)
                                                                                    `(|...| (ref ,xs)))) ...) ,maybe-fail-to ...
                ,body)

              (define-values (body-expr body-new-defs body-free) (clo-convert-ast body))

              (define xs-to-remove (set-union (set fallback-x arg-count-x) (list->set xs) global-names reserved-bl-x))
              (define def-free-vars
                (set->list
                  (set-subtract body-free xs-to-remove)))

              (define def+
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,@maybe-fail-to ,body-expr))

              (values
                (def-group (append (def-group-defs curr-def-group) (list def+))
                           (set-union (list->set def-free-vars) (def-group-free-vars curr-def-group)))
                (set-union body-new-defs new-defs))])))
      
      (values
        (set-add def-groups def-g)
        (set-union new-defs more-new-defs))))

  ;; Fully closure convert defs: each def that is first in its group becomes an __apply__
  ;; and passes around a closure for the entire group.
  (define-values (closure-bindings lifted-defs free-vars)
    (for*/fold ([closure-bindings (list)]
                [lifted-defs (set)]
                [free-vars (set)])
               ([curr-def-group def-groups]
                #:do [(define group-free-vars (set->list (def-group-free-vars curr-def-group)))] ;; pick an arbitrary ordering for the free vars to put into the closure
                [def (def-group-defs curr-def-group)])

      (define clo-x (gensymb 'clo))
      (define clo-slice-x (gensymb 'clo_slice))

      (match def
        ;; First def in group: convert to an __apply__
        [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body)
          #:when (is-first-def-in-group? curr-def-group def)

          (define clo-object-tag (gensymb 'clo))
          (define escaped-clo-object-tag (escape-id-for-C clo-object-tag))
          (define new-apply-x (gensymb apply-x))
          (define escaped-new-apply-x (escape-id-for-C new-apply-x))

          (define new-def-body
            `(let (ref ,clo-slice-x) (bless ((ref get_object_slice) (ref ,clo-x)))
                ,(unpack-clo clo-slice-x group-free-vars body)))

          (define new-lifted-def
            `(def ((ref ,escaped-new-apply-x) (ref ,fallback-x) (ref ,arg-count-x) (ref ,clo-x) ,@params) ,@maybe-fail-to ,new-def-body))

          ;; Closure object
          (define make-clo
            `(object
              (ref ,escaped-clo-object-tag)
              ,@(map (lambda (x) `(ref ,x)) group-free-vars)))

          ;; Use unescaped names when registering (they are escaped later on)
          (register-type! clo-object-tag)
          (register-method! apply-x clo-object-tag new-apply-x)

          (values
              (cons `((ref ,fx) ,make-clo) closure-bindings)
              (set-add lifted-defs new-lifted-def)
              (set-union (list->set group-free-vars) free-vars))]

        ;; Not first def in group
        [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,maybe-fail-to ... ,body)

          (define new-def-body
            `(let (ref ,clo-slice-x) (bless ((ref get_object_slice) (ref ,clo-x)))
                  ,(unpack-clo clo-slice-x group-free-vars body)))

          (define new-lifted-def
            `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) (ref ,clo-x) ,@params) ,@maybe-fail-to ,new-def-body))

          (values
              closure-bindings
              (set-add lifted-defs new-lifted-def)
              (set-union (list->set group-free-vars) free-vars))])))

  (define def-names (get-def-names defs))

  (values
    `(closures ,closure-bindings
       ,rest-expr)
    (set-union lifted-defs lifted-defs-from-bodies rest-new-defs)
    (set-subtract (set-union free-vars rest-free) def-names)))


;; Symbol (ListOf Symbol) Expr -> Expr
(define (unpack-clo clo-slice-x xs body)
  (match xs
    ['() body]
    [`(,a)
      `(let (ref ,a) ((ref _first) (ref _none) (bless (const 1)) (ref ,clo-slice-x))
          ,body)]
    [`(,a . ,b)
      (define clo-slice-rest-x (gensymb 'clo_rest))

      `(let (ref ,a) ((ref _first) (ref _none) (bless (const 1)) (ref ,clo-slice-x))
        (let (ref ,clo-slice-rest-x) ((ref _rest) (ref _none) (bless (const 1)) (ref ,clo-slice-x))
          ,(unpack-clo clo-slice-rest-x b body)))]))

(define (with-print-value val-ast ast)
  `(let (ref ,(gensymb '_))
        (bless ((ref print_debug_value) ,val-ast))
        ,ast))