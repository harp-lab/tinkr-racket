#lang racket

(provide is-bless-primitive?
         get-bless-primitive-fun
         bless-primitive-has-fun?
         bless-primitive-has-no-effect?
         bless-primitive-is-truthy?)

;; TODO: maybe handle arity and other invalid applications?

(struct bless-primitive
  [fun                ;; (or #f Function)
   truthy?            ;; Bool
   maybe-effectful?]  ;; Bool
  #:transparent)

(define (bp-eq v1 v2)
  (match* (v1 v2)
    [(`(const ,c1) `(const ,c2))
      (if (equal? c1 c2)
          `(const 1)
          `(const 0))]
    [(_ _) #f]))

(define (bp-equal v1 v2)
  (match* (v1 v2)
    [(`(const ,c1) `(const ,c2))
      (if (equal? c1 c2)
          `(const true)
          `(const false))]
    [(_ _) #f]))

(define (is-bless-primitive? prim-id)
  (hash-has-key? bless-primitives prim-id))

(define (get-bless-primitive-fun prim-id)
  (bless-primitive-fun (hash-ref bless-primitives prim-id)))

(define (bless-primitive-has-fun? prim-id)
  (and (hash-has-key? bless-primitives prim-id)
       (bless-primitive-fun (hash-ref bless-primitives prim-id))))

(define (bless-primitive-has-no-effect? prim-id)
  (and (hash-has-key? bless-primitives prim-id)
       (not (bless-primitive-maybe-effectful? (hash-ref bless-primitives prim-id)))))

(define (bless-primitive-is-truthy? prim-id)
  (and (hash-has-key? bless-primitives prim-id)
       (bless-primitive-truthy? (hash-ref bless-primitives prim-id))))

(define bless-primitives
  (hash
    'eq     (bless-primitive bp-eq #t #f)     ;; TODO: should eq be truthy?
    'equal  (bless-primitive bp-equal #f #f)))

(module+ test
  (require rackunit)

  (check-equal? (bp-eq `(const 1) `(const 1)) `(const 1))
  (check-equal? (bp-eq `(const 1) `(const 2)) `(const 0))
  (check-false (bp-eq `(const 1) `(extern-ref x)))

  (check-equal? (bp-equal `(const 1) `(const 1)) `(const true))
  (check-equal? (bp-equal `(const 1) `(const 2)) `(const false))
  (check-false (bp-equal `(extern-ref x) `(const 2)))

  (check-true (bless-primitive-is-truthy? 'eq))
  (check-false (bless-primitive-is-truthy? 'equal))
  (check-true (bless-primitive-has-no-effect? 'equal))

  ;; Unknown blessed prims are conservatively treated as effectful and not truthy
  (check-false (is-bless-primitive? 'unknown))
  (check-false (bless-primitive-has-fun? 'unknown))
  (check-false (bless-primitive-has-no-effect? 'unknown))
  (check-false (bless-primitive-is-truthy? 'unknown)))
