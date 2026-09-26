#lang racket

(provide is-primitive?
         get-primitive-fun
         primitive-has-fun?
         primitive-has-no-effect?
         primitive-is-truthy?)

(require "inlining-helpers.rkt")

;; TODO: maybe handle arity and other invalid applications?

(struct primitive
  [fun                ;; (or #f Function)
   truthy?            ;; Bool
   maybe-effectful?]  ;; Bool
  #:transparent)

;; Var -> (or #f Expr)
(define (get-es-if-slice x)
  (match-define (var x-sym op flags source-flags) x)

  (if (list? op)
      (let ([op-es (map (lambda (op) (visit-op-cache op)) op)])
        (if (andmap (lambda (e) (and e (copyable? e))) op-es)
          (begin
            (hash-set! flags 'ref (hash-ref flags 'ref 0))
            op-es)
          #f))
      #f))

(define (dec-ref-flag! x)
  (match-define (var x-sym op flags source-flags) x)

  (when (hash-has-key? flags 'ref)
    (dec-flag! flags 'ref)))

(define (p-slice-concat fallback arg-count v1 v2)
  (match* (v1 v2)
    [(`(|[]| ,xs ...) `(|[]| ,ys ...))
      `(|[]| ,@xs ,@ys)]
    
    ;; Empty slices
    ;; This should be safe since _slice_concat should only ever be called internally,
    ;; so "any" should result in a slice (and so we don't need to worry about raising an
    ;; error when "any is not a slice).
    [(any `(|[]|))
      any]
    [(`(|[]|) any)
      any]

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

;; Expr Expr Expr -> (or #f Expr)
;; Turns an indirect application of f on a statically known arg slice into a direct call.
(define (make-direct-call f fb arg-list)
  (define f-ok?
    (match f
      [(or `(ref ,_) `(fallback-ref ,_) `(extern-ref ,_)) #t]
      [_ #f]))

  (define args
    (and f-ok?
      (match arg-list
        [`(|[]| ,xs ...) xs]

        ;; x might be bound to a slice
        [`(ref ,x)
          (define res (get-es-if-slice x))
          (when res (dec-ref-flag! x))
          res]

        [_ #f])))

  (and args
    `(,f ,fb (bless (const ,(length args))) ,@args)))

(define (p-apply fallback arg-count f arg-list)
  (make-direct-call f '(extern-ref none) arg-list))

(define (p-apply-with-fallback fallback arg-count f fb arg-list)
  (define fb^
    (match fb
      [`(const void) '(extern-ref none)]
      [_ fb]))

  (make-direct-call f fb^ arg-list))

(define (is-primitive? prim-id)
  (hash-has-key? primitives prim-id))

(define (get-primitive-fun prim-id)
  (primitive-fun (hash-ref primitives prim-id)))

(define (primitive-has-fun? prim-id)
  (and (hash-has-key? primitives prim-id) (primitive-fun (hash-ref primitives prim-id))))

(define (primitive-has-no-effect? prim-id)
  (and (hash-has-key? primitives prim-id)
       (not (primitive-maybe-effectful? (hash-ref primitives prim-id)))))

(define (primitive-is-truthy? prim-id)
  (and (hash-has-key? primitives prim-id)
       (primitive-truthy? (hash-ref primitives prim-id))))

(define primitives
  (hash
    '_slice_concat          (primitive p-slice-concat #t #f)
    '_apply                 (primitive p-apply #f #t)
    '_apply_with_fallback   (primitive p-apply-with-fallback #f #t)
    '_init_from_s64         (primitive #f #t #f)))

;; Some unit tests thanks to Claude:
(module+ test
  (require rackunit)

  (define fallback '(const void))
  (define arg-count '(bless (const 2)))

  ;; Symbol (ListOf Expr) -> Var
  ;; A var bound to a variadic operand (i.e. a slice) whose elements have already been visited
  (define (slice-var name es)
    (var name
         (map (lambda (e) (opnd e (box #f) (box e))) es)
         (make-hash '((ref . 1)))
         (hash)))

  ;; Symbol -> Var
  ;; A var that isn't bound to anything
  (define (unbound-var name)
    (var name #f (make-hash '((ref . 1))) (hash)))

  (define (ref-count x)
    (hash-ref (var-flags x) 'ref))

  ;; --- _slice_concat

  (check-equal? (p-slice-concat fallback arg-count '(|[]| (const 1)) '(|[]| (const 2) (const 3)))
                '(|[]| (const 1) (const 2) (const 3)))
  (check-equal? (p-slice-concat fallback arg-count '(|[]|) '(|[]|))
                '(|[]|))

  ;; Concat with an empty slice returns the other argument, even if it isn't statically known
  (check-equal? (p-slice-concat fallback arg-count '(extern-ref xs) '(|[]|))
                '(extern-ref xs))
  (check-equal? (p-slice-concat fallback arg-count '(|[]|) '(extern-ref xs))
                '(extern-ref xs))

  ;; Var bound to a slice gets spliced in and its ref count decremented
  (let ([x (slice-var 'x '((const 2) (const 3)))])
    (check-equal? (p-slice-concat fallback arg-count '(|[]| (const 1)) `(ref ,x))
                  '(|[]| (const 1) (const 2) (const 3)))
    (check-equal? (ref-count x) 0))
  (let ([x (slice-var 'x '((const 1) (const 2)))])
    (check-equal? (p-slice-concat fallback arg-count `(ref ,x) '(|[]| (const 3)))
                  '(|[]| (const 1) (const 2) (const 3)))
    (check-equal? (ref-count x) 0))

  ;; Var not bound to a slice: no reduction and ref count untouched
  (let ([x (unbound-var 'x)])
    (check-false (p-slice-concat fallback arg-count '(|[]| (const 1)) `(ref ,x)))
    (check-equal? (ref-count x) 1))

  ;; Slice element that isn't copyable: no reduction and ref count untouched
  (let ([x (slice-var 'x '((const 1) ((extern-ref f) (extern-ref none) (bless (const 0)))))])
    (check-false (p-slice-concat fallback arg-count '(|[]| (const 0)) `(ref ,x)))
    (check-equal? (ref-count x) 1))

  ;; Neither side is a literal slice
  (let ([x (slice-var 'x '((const 1)))]
        [y (slice-var 'y '((const 2)))])
    (check-false (p-slice-concat fallback arg-count `(ref ,x) `(ref ,y))))

  ;; --- _apply

  ;; Direct call includes the fallback and arg_count slots
  (check-equal? (p-apply fallback arg-count '(extern-ref f) '(|[]| (const 1) (const 2)))
                '((extern-ref f) (extern-ref none) (bless (const 2)) (const 1) (const 2)))
  (check-equal? (p-apply fallback arg-count '(extern-ref f) '(|[]|))
                '((extern-ref f) (extern-ref none) (bless (const 0))))
  (check-equal? (p-apply fallback arg-count '(fallback-ref f) '(|[]| (const 1)))
                '((fallback-ref f) (extern-ref none) (bless (const 1)) (const 1)))
  (let ([f (unbound-var 'f)])
    (check-equal? (p-apply fallback arg-count `(ref ,f) '(|[]| (const 1)))
                  `((ref ,f) (extern-ref none) (bless (const 1)) (const 1))))

  ;; Var bound to a slice
  (let ([x (slice-var 'x '((const 1) (const 2) (const 3)))])
    (check-equal? (p-apply fallback arg-count '(extern-ref f) `(ref ,x))
                  '((extern-ref f) (extern-ref none) (bless (const 3)) (const 1) (const 2) (const 3)))
    (check-equal? (ref-count x) 0))

  ;; Unknown args
  (let ([x (unbound-var 'x)])
    (check-false (p-apply fallback arg-count '(extern-ref f) `(ref ,x)))
    (check-equal? (ref-count x) 1))
  (check-false (p-apply fallback arg-count '(extern-ref f) '((extern-ref g) (extern-ref none) (bless (const 0)))))

  ;; Callee isn't a reference
  (check-false (p-apply fallback arg-count '((extern-ref g) (extern-ref none) (bless (const 0))) '(|[]| (const 1))))

  ;; --- _apply_with_fallback

  ;; The fallback is passed through to the direct call
  (let ([fb (unbound-var 'fb)])
    (check-equal? (p-apply-with-fallback fallback arg-count '(extern-ref f) `(ref ,fb) '(|[]| (const 1) (const 2)))
                  `((extern-ref f) (ref ,fb) (bless (const 2)) (const 1) (const 2))))
  (check-equal? (p-apply-with-fallback fallback arg-count '(extern-ref f) '(extern-ref none) '(|[]| (const 1)))
                '((extern-ref f) (extern-ref none) (bless (const 1)) (const 1)))

  ;; A void fallback becomes none
  (check-equal? (p-apply-with-fallback fallback arg-count '(extern-ref f) '(const void) '(|[]|))
                '((extern-ref f) (extern-ref none) (bless (const 0))))

  ;; Var bound to a slice
  (let ([x (slice-var 'x '((const 1) (const 2)))])
    (check-equal? (p-apply-with-fallback fallback arg-count '(fallback-ref f) '(extern-ref none) `(ref ,x))
                  '((fallback-ref f) (extern-ref none) (bless (const 2)) (const 1) (const 2)))
    (check-equal? (ref-count x) 0))

  ;; Unknown args
  (let ([x (unbound-var 'x)])
    (check-false (p-apply-with-fallback fallback arg-count '(extern-ref f) '(extern-ref none) `(ref ,x)))))
