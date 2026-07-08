#lang racket

(provide clo-convert-mod)

;; AlphatizedModule -> CloModule
(define (clo-convert-mod mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define defs+
       (foldr append '() ;; flatten one level
        (for/list ([ast defs]) 
          (clo-convert ast))))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs+ ,methods ,types)]))

;; Expr -> (ListOf Expr)
(define (clo-convert def-ast)
  (match def-ast
    [`(def (,xs ...) ,body)
      (define-values (expr new-defs _) (clo-convert-ast body))
      (append (list `(def (,@xs) ,expr)) (set->list new-defs))]
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
        `(if ,g-expr ,t-expr ,e-expr)
        (set-union g-defs e-defs t-defs)
        (set-union g-free e-free t-free))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es
                   (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail ,fail-ref)
      (recur fail-ref
             (lambda (e) `(fail ,e)))]

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

    ;; slices
    [`(|[]| ,es ...)
      (recur-exprs es
                   (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def ((ref ,fx) ,xs ...) ,body ,more)
      (clo-convert-inner-def ast)]

    ;; Untagged application
    [`((ref ,fx) ,es ...)
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

      (values
        `(,fx-expr ,@new-es)
        (set-union fx-defs es-defs)
        (set-union fx-free es-free))]))


;; Expr -> (ValuesOf Expr (SetOf Expr) (SetOf Variable))
(define (clo-convert-inner-def def-ast)
  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-sibling-inner-defs def-ast))

  ;; Assume only one def for now (TODO: handle more than one def)
  (define def (first defs))

  (match def
    [`(def ((ref ,fx) (ref ,xs) ...) ,body)
      (define-values (body-expr body-new-defs body-free) (clo-convert-ast body))

      (define-values (rest-expr rest-new-defs rest-free) (clo-convert-ast rest-ast))

      ;; TODO: change to an apply def
      (define new-def
        `(def ((ref ,fx) ,@(map (lambda (x) `(ref ,x)) xs)) ,body-expr))

      (define new-def-free
        (set-subtract body-free (list->set xs)))

      (values
          rest-expr ;; TODO: make closure object here
          (set-union (set-add body-new-defs new-def) rest-new-defs)
          (set-union new-def-free rest-free))]))

;; Expr -> (ValuesOf (ListOf Expr) Expr)
(define (get-sibling-inner-defs def-ast)
  (match def-ast
    [`(def ((ref ,x) ,args ...) ,body ,more)
      (define-values (defs rest) (get-sibling-inner-defs more))

      (values
        (append
          (list `(def ((ref ,x) ,@args) ,body))
          defs)
        rest)]
    
    [_ 
      (values
        '()
        def-ast)]))
