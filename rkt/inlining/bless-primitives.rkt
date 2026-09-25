#lang racket

(provide bless-primitives)

(define (bp-eq v1 v2)
  (if (equal? v1 v2)
      `(const 0)
      `(const 1)))

(define (bp-equal v1 v2)
  (if (equal? v1 v2)
      `(const true)
      `(const false)))

(define bless-primitives
  (hash
    'eq bp-eq
    'equal bp-equal))

(module+ test
  (require rackunit)
  
  (check-equal? (bp-equal `(const 1) `(const 1)) `(const true))
  (check-equal? (bp-equal `(const 1) `(const 2)) `(const false)))
