#lang racket

(require "utils.rkt")

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
     (define args-x (gensymb 'args))
     (define apply-fun-ptr-x (gensymb 'apply_fun_ptr))

     (define apply-fun-ptr-def
      `(def ((ref ,(escape-id-for-C apply-fun-ptr-x)) (ref ,(gensymb 'fallback)) (ref ,(gensymb 'arg_count)) (ref ,fun-ptr-x) (... (ref ,args-x)))
        ((ref _apply_on_slice) (ref ,fun-ptr-x) (ref ,args-x))))
    
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
    [`(bless ,e0) (values ast (set) (set))] ;; TODO: handle bless

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
        (if (equal? fx '_u__init__from__s64) ;; TODO: this is a temporary fix, do this for all global symbols
          `(,fx-expr ,fallback ,arg-count ,@new-es)

          (match fallback
            [`(ref _none)
              `((ref ,escaped-apply-x) (ref _none) (bless (const ,(length new-es))) ,fx-expr ,@new-es)] ;; The arg count here is for applying fx (so it is only the length of new-es)
            [_
              ;; If passing something other than none, then it must be a regular function
              ;; TODO: is this case ever hit?
              `(,fx-expr ,fallback ,arg-count ,@new-es)])))

      (values
        app-expr
        (set-union fx-defs es-defs)
        (set-union fx-free es-free))]))


;; Expr -> (ValuesOf Expr (SetOf Expr) (SetOf Variable))
(define (clo-convert-inner-def def-ast)
  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-sibling-inner-defs def-ast))

  (define-values (rest-expr rest-new-defs rest-free) (clo-convert-ast rest-ast))

  ;; A set of lists of def names which are linked together in a fail chain by fail_to.
  ;; The first def in a chain is the entry point.
  (define fail-chains
    (for/fold ([chains (set)])
              ([def defs])
      (match def
        [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body)
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
                      (values
                        (set-add updated-chains (append chain (list maybe-fail-x))) ;; Extend existing chain
                        #t)
                      (values
                        (set-add updated-chains chain)
                        updated))))
              
              (if updated
                  updated-chains
                  (set-add chains (list fx maybe-fail-x)))] ;; Start new chain
            
            ;; This def's name (i.e. fx) will have already been added to a chain
            [else chains])])))

  (define (get-def-with-name fx)
    (define (def-name-maches? def)
      (match def
        [`(def ((ref ,gx) ,_ ...) ,_ ... ,_) (equal? fx gx)]))

    (for/first ([def defs]
                #:when (def-name-maches? def))
      def))

  (struct def-group
    [defs        ;; (ListOf Expr)
     free-vars]  ;; (SetOf Variable)
    #:transparent)

  ;; Closure convert def bodies and find free vars for each def group
  (define-values (def-groups lifted-defs-from-bodies)
    (for/fold ([def-groups (set)]
               [new-defs (set)])
              ([chain fail-chains])
      (define-values (def-g more-new-defs)
        (for/fold ([curr-def-group (def-group (list) (set))]
                  [new-defs (set)])
                  ([def-name chain])

          (define def (get-def-with-name def-name))
          
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,(and params (or `(ref ,xs)
                                                                                    `(|...| (ref ,xs)))) ...) ,maybe-fail-to ...
                ,body)

              (define-values (body-expr body-new-defs body-free) (clo-convert-ast body))

              (define def-free-vars
                (set->list
                  (set-subtract body-free (list->set xs))))

              (define def+
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,@maybe-fail-to ,body-expr))

              (values
                (def-group (append (def-group-defs curr-def-group) (list def+))
                           (set-union (list->set def-free-vars) (def-group-free-vars curr-def-group)))
                (set-union body-new-defs new-defs))])))
      
      (values
        (set-add def-groups def-g)
        (set-union new-defs more-new-defs))))

  (define (is-first-def-in-group? group def)
    (equal? def
            (first (def-group-defs group))))

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
            `(if (bless ((ref equal) ((ref get_object_tag) (ref ,clo-x))
                                      (ref ,escaped-clo-object-tag)))
                (let (ref ,clo-slice-x) (bless ((ref get_object_slice) (ref ,clo-x)))
                  ,(unpack-clo clo-slice-x group-free-vars body))
                
                (fail))) ;; TODO: do we need this check and fail?

          (define new-lifted-def
            `(def ((ref ,escaped-new-apply-x) (ref ,fallback-x) (ref ,arg-count-x) (ref ,clo-x) ,@params) ,@maybe-fail-to ,new-def-body))

          ;; Closure object
          (define make-clo
            `(object
              (ref ,escaped-clo-object-tag)
              ,@(map (lambda (x) `(ref ,x)) group-free-vars)))

          ;; Use unescaped names when registering (they are escaped later on)
          ;; TODO: maybe refactor to do all the id escaping in alphatize instead of doing some of it in link.rkt
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

  (values
    `(closures ,closure-bindings
       ,rest-expr)
    (set-union lifted-defs lifted-defs-from-bodies rest-new-defs)
    (set-union free-vars rest-free)))

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

;; Expr -> (ValuesOf (ListOf Expr) Expr)
(define (get-sibling-inner-defs def-ast)
  (match def-ast
    [`(def ((ref ,x) ,args ...) ,maybe-fail-to ... ,body ,more)
      (define-values (defs rest) (get-sibling-inner-defs more))

      (values
        (append
          (list `(def ((ref ,x) ,@args) ,@maybe-fail-to ,body))
          defs)
        rest)]
    
    [_ 
      (values
        '()
        def-ast)]))

(define (with-print-value val-ast ast)
  `(let (ref ,(gensymb '_))
        (bless ((ref print_debug_value) ,val-ast))
        ,ast))