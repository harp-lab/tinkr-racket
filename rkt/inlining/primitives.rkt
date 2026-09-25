#lang racket

(provide primitives)

(require "inlining-helpers.rkt")

;; TODO: maybe handle arity and other invalid applications?

;; Var -> (or #f Expr)
(define (get-es-if-slice x)
  (match-define (var x-sym op flags source-flags) x)

  (if (list? op)
      (let ([op-es (map (lambda (op) (visit-op-cache op)) op)])
        (if (andmap copyable? op-es)
          (begin
            (hash-set! flags 'ref (hash-ref flags 'ref 0))
            op-es)
          #f))
      #f))

(define (dec-ref-flag! x)
  (match-define (var x-sym op flags source-flags) x)

  (when (hash-has-key? flags 'ref)
      (displayln "dec-ref-flag!:")
      (displayln (hash-ref flags 'ref)))

  (when (hash-has-key? flags 'ref)
    (dec-flag! flags 'ref)))

(define (p-slice-concat fallback arg-count v1 v2)
  (displayln "call to slice concat")
  (displayln v1)
  (displayln v2)

  (match* (v1 v2)
    [(`(|[]| ,xs ...) `(|[]| ,ys ...))
      `(|[]| ,@xs ,@ys)]
    
    ;; x might be bound to a slice
    [(`(|[]| ,xs ...) `(ref ,x))
      (define res (get-es-if-slice x))
      (when res (dec-ref-flag! x))
      (if res
          `(|[]| ,@xs ,@res)
          #f)]
    [(`(ref ,x) `(|[]| ,xs ...))
      (define res (get-es-if-slice x))
      (when res (dec-ref-flag! x))
      (if res
          `(|[]| ,@res ,@xs)
          #f)]
    
    [(_ _) #f]))

(define (p-apply fallback arg-count v1 v2)
  (displayln "call to apply")
  (match* (v1 v2)
    [(`(ref ,fx) `(|[]| ,xs ...))
      `((ref ,fx) ,@xs)]
    
    ;; x might be bound to a slice
    [(`(ref ,fx) `(ref ,x))
      (define res (get-es-if-slice x))
      (when res (dec-ref-flag! x))
      (if res
          `((ref ,fx) ,@res)
          #f)]
    
    [(_ _) #f]))

(define primitives
  (hash
    '_slice_concat p-slice-concat
    '_apply p-apply))