#lang racket

(provide get-nested-sibling-defs
         nest-sibling-defs
         get-def-name
         get-def-names
         get-def-with-name
         get-fail-chains)


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


;; (ListOf Expr) -> (SetOf Symbol)
(define (get-def-names defs)
  (for/set ([def defs])
      (get-def-name def)))

;; (ListOf Expr) Symbol -> Expr
(define (get-def-with-name defs fx)
    (define (def-name-maches? def) (equal? fx (get-def-name def)))

    (for/first ([def defs]
                #:when (def-name-maches? def))
      def))

;; Expr -> Symbol
(define (get-def-name def)
  (match def
    [`(def ((ref ,fx) ,params ...) ,body ...)
      fx]))


;; (ListOf Expr) -> (SetOf (ListOf Symbol))
;; A set of lists of def names which are linked together in a fail chain by fail_to.
;; The first def in a chain is the entry point.
(define (get-fail-chains defs)
  (for/fold ([chains (set)])
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