#lang racket

(provide get-nested-sibling-defs
         nest-sibling-defs)

;; Expr -> (ValuesOf (ListOf Expr) Expr)
;; Split the nested sibling defs into a list of seperate defs (and a final rest-ast).
(define (get-nested-sibling-defs def-ast)
  (match def-ast
    [`(def ((ref ,fx) ,params ...) ,body ... ,more)
      (define-values (defs rest) (get-nested-sibling-defs more))

      (values
        (append
          (list `(def ((ref ,fx) ,@params) ,@body))
          defs)
        rest)]
    
    [_ 
      (values
        '()
        def-ast)]))

;; (ListOf Expr) Expr -> Expr
;; Opposite of "get-nested-sibling-defs". Nests the defs back together with rest-ast at the center.
(define (nest-sibling-defs defs rest-ast)
  (for/fold ([inner-ast rest-ast])
            ([def (reverse defs)])
    (match def
      [`(def ((ref ,fx) ,params ...) ,body ...)
        `(def ((ref ,fx) ,@params) ,@body ,inner-ast)])))