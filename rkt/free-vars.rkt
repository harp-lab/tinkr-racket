#lang racket

(require "simplify.rkt"
         "helpers.rkt")

(provide annotate-with-free-vars)

;; AlphatizedModule -> AnnotatedFreeVarsMod
(define (annotate-with-free-vars mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+ (map free-vars/def defs))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs+ ,methods ,types)]))

;; Expr -> Expr
(define (free-vars/def def-ast)
  (match def-ast
    [`(def (,xs ...) ,maybe-fail-to ... ,body)
     (define-values (body+ free) (free-vars/ast body))
     `(def (,@xs) (,@maybe-fail-to) ,body+)]
    [_ (error 'free-vars/def)]))

;; Expr -> (ValuesOf Expr (SetOf Symbol))
;; Walk ast and return new ast with free var annotations and
;; a set of free vars for the ast.
(define (free-vars/ast ast)
  (define (recur ast outer-expr)
    (define-values (expr free) (free-vars/ast ast))
    (values
      (outer-expr expr)
      free))

  (define (recur-exprs asts outer-expr)
    (define-values (exprs free)
      (for/foldr ([exprs (list)]
                  [free (set)])
                 ([ast asts])
        (define-values (expr new-free) (free-vars/ast ast))
        
        (values
          (cons expr exprs)
          (set-union free new-free))))

    (values
      (outer-expr exprs)
      free))

  (match ast
    [`(ref ,x) (values ast (set x))]
    [`(const ,_) (values ast (set))]
    
    ;; Bless
    [`(bless ,e0)
      (define (freebless ast)
        (match ast
          [`(ref ,x) (set x)]
          [`((ref ,fx) ,aes ...) ;; do not count fun-expr
            (foldl set-union (set) (map freebless aes))]
          [_ (set)]))

      (values ast (freebless e0))]

    [`(if ,g ,t ,e)
      (recur-exprs (list g t e) (lambda (es) `(if ,@es)))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail) (values ast (set))]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (recur e0 (lambda (e0) `(,ell ,e0)))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-exprs es (lambda (es) `(,ctor ,@es)))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (define-values (rhs+ rhs-free) (free-vars/ast rhs))
      (define-values (body+ body-free) (free-vars/ast body))

      (values
        `(let (ref ,x) ,rhs+ ,body+)
        (set-union rhs-free (set-remove body-free x)))]

    ;; Slices
    [`(|[]| ,es ...)
      (recur-exprs es (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def ((ref ,fx) ,params ...) ,maybe-fail-to ... ,body ,more)
      (free-vars/inner-def ast)]

    ;; Untagged application
    [`(,es ...)
      (recur-exprs es (lambda (es) `(,@es)))]))


;; Expr -> (ValuesOf Expr (SetOf Symbol))
(define (free-vars/inner-def def-ast)
  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-nested-sibling-defs def-ast))

  (define-values (defs+ defs-free)
    (for/foldr ([defs+ (list)]
                [free-acc (set)])
               ([def (in-list defs)])
      (match def
        [`(def ((ref ,fx) ,(and params (or `(ref ,xs)
                                          `(|...| (ref ,xs)))) ...) ,maybe-fail-to ... ,body)

          (define-values (body+ body-free) (free-vars/ast body))

          ;; Note: intentionally keeping fx in the freevars for the annotation (for the case of closure conversion),
          (define xs-to-remove (set-union (list->set xs) global-names reserved-bl-x)) ;; Remove params and global names
          (define free-for-def (set-subtract body-free xs-to-remove))
          (define free-for-def-refs (map (lambda (fv) `(ref ,fv)) (set->list free-for-def)))
          
          (values
            (cons `(def ((ref ,fx) ,@params) ((free_vars ,@free-for-def-refs) ,@maybe-fail-to) ,body+) defs+)
            (set-union free-acc free-for-def))])))

  (define def-names
    (for/set ([def (in-list defs)])
      (get-def-name def)))

  (define-values (rest-ast+ rest-ast-free) (free-vars/ast rest-ast))

  (define total-free (set-subtract (set-union defs-free rest-ast-free) def-names))

  (values
    (nest-sibling-defs defs+ rest-ast+)
    total-free))