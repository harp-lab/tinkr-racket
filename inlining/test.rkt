#lang racket

(require rackunit "inlining.rkt")

(define default-effort-bound 100)
(define default-size-bound 30)
(set-effort-bound! default-effort-bound)
(set-size-bound! default-size-bound)

;; ----- Helpers -----

(define (alpha-equiv? p0 p1)
  (equal? (alphatize p0) (alphatize p1)))

(define (ast-size ast)
  (match ast
    [(list e ...) (+ 1 (apply + (map ast-size e)))]
    [(cons e1 e2) (+ 1 (ast-size e1) (ast-size e2))]
    [_ 1]))

(define default-iterations 1)

(define (larger? p)
  (> (ast-size (optimize-prog p default-iterations)) (ast-size p)))

(define (smaller? p)
  (< (ast-size (optimize-prog p default-iterations)) (ast-size p)))

(define (no-change? p)
  (alpha-equiv? (optimize-prog p default-iterations) p))

;; ----- Test Cases -----

(define p1
  `((lambda (x) x) 5))

(check-equal? (optimize-prog p1) 5)

(define p2
  `(lambda (a)
    (let ([x 3])
      (if (zero? a)
          x
          5))))

(check-equal? (alpha-equiv? (optimize-prog p2) '(lambda (a3243) (if (zero? a3243) 3 5)))
              #t)
(check-equal? ((eval (optimize-prog p2)) 0) ((eval p2) 0))

(define p3
  `((lambda (x)
      ((lambda (f)
        (f 6))
       (lambda (y)
        (x y))))
    (lambda (z) z)))

(check-equal? (eval (optimize-prog p3)) (eval p3))

(define p4
  `(((lambda (x)
      (lambda (y)
        (if (zero? y)
            (x y)
            (add1 (x y)))))
     (lambda (z) z))
    1))

(check-equal? (eval (optimize-prog p4)) (eval p4))

(define p5
 '(let ([f (lambda (g) (g g))])
    (let ([z (lambda (n) (if (< n 10) (lambda (x) 5) (lambda (x) 15)))])
      (let ([y (lambda (m) (m 4))])
        (let ([x (y z)])
          (+ 7 (f x)))))))

(check-equal? (eval (optimize-prog p5)) (eval p5))
(check-equal? (optimize-prog p5 1) '12) ;; See section 4.3 of cp0 paper to solve this.

(define p6
  `(let ([f (lambda (a b)
            (a b))])
      (f (lambda (x) x) 1)))

(check-equal? (eval (optimize-prog p6)) (eval p6))

(define p7
 '(lambda (h)
    (let ([f (lambda (g) (g g))])
      (let ([z (lambda (n) (if (< n 10) (lambda (x) 5) (lambda (x) 15)))])
        (let ([y (lambda (m) (m 4))])
          (let ([x (h (y z))])
            (+ 7 (f x))))))))

(check-equal? ((eval (optimize-prog p7)) (lambda (x) x)) ((eval p7) (lambda (x) x)))

(define p8
  `((lambda (x) (x x)) (lambda (x) (x x))))

(check-equal? (no-change? p8) #t)

(define p9
  `(lambda (args)
     (let ([x (foo 1000)])
      (+ x x))))

;; Should not change since we don't want to duplicate the work of (foo 1000).
(check-equal? (no-change? p9) #t)

(define p10
  `((lambda (x)
     (+ (x 5) (x 5)))
    foo))

(check-equal? (smaller? p10) #t)

(define p-alpha
  `(let ([x 0])
    (let ([f (lambda (x)
              (let ([g (lambda (x) x)])
                (g (add1 x))))])
      (f 9))))

(check-equal? (optimize-prog p-alpha) '10)

;; Letrec test cases

(define letrec-1
  `(letrec ([fact (lambda (n)
                    (if (< n 2)
                        1
                        (* n (fact (- n 1)))))])
    (fact 5)))

(check-equal? (no-change? letrec-1) #t)

(define letrec-2
  `(letrec ([fact (lambda (n)
                    (let ([base-case 1])
                      (if (< n 2)
                          base-case
                          (* n (fact (- n 1))))))])
    (fact 5)))

(check-equal? (smaller? letrec-2) #t)

(define letrec-3
  `(letrec ([f (lambda (x) (if (zero? x) 1 (* x (f (- x 1)))))]
            [g (displayln "world")]
            [a (lambda (x) (b x))]
            [b (lambda (x) (a x))])
    (f 5)))

(check-equal? (smaller? letrec-3) #t) ;; TODO: This needs more advanced letrec handling

(define letrec-4
  `(letrec ([a b]
            [b 1]
            [c 2]
            [d a]
            [e (+ a b c d)])
    (+ e 1)))

(check-equal? (alpha-equiv? (optimize-prog letrec-4 default-iterations)
                            '(letrec [(a 1) (b 1) (c 2) (d 1) (e 5)] 6))
              #t)

;; Effort bound test cases

;; 8 calls to f
(define p-e7
  `(let ([f (lambda (f) (+ (f 5) (f 5) (f 5)))])
    (let ([g1
      (lambda (g1)
        (let ([g2
          (lambda (g2)
            (+ (g2 (lambda (k) k)) (g2 (lambda (k) (add1 k)))))])
          (+ (g2 g1) (g2 g1))))])
      (+ (g1 f) (g1 f)))))

;; Should be 128 calls to f
(define p-e8
  `(let ([f (lambda (f) (+ (f 5) (f 5) (f 5)))])
    (let ([g1
      (lambda (g1)
        (let ([g2
          (lambda (g2)
            (let ([g3
              (lambda (g3)
                (let ([g4
                  (lambda (g4)
                    (let ([g5
                      (lambda (g5)
                        (let ([g6
                          (lambda (g6)
                            (+ (g6 (lambda (k) k)) (g6 (lambda (k) k))))])
                          (+ (g6 g5) (g6 g5))))])
                      (+ (g5 g4) (g5 g4))))])
                  (+ (g4 g3) (g4 g3))))])
              (+ (g3 g2) (g3 g2))))])
          (+ (g2 g1) (g2 g1))))])
      (+ (g1 f) (g1 f)))))

;; TODO: add automated tests for effort bound

;; Size bound tests

;; p-s1 should not inline y because it is too large
(define p-s1
  `(let ([y (lambda (x) (+ 0 0 0 0 0 0 0 0 0 0 0 0 0
                           0 (x (lambda (i) i))))])
    (lambda (x) (+ (y x) (y x) (y x) (y x)))))

;; p-s2 should inline y because it is small enough
(define p-s2
  `(let ([y (lambda (x) (+ 0 (x (lambda (i) i))))])
    (lambda (x) (+ (y x) (y x) (y x) (y x)))))

;; p-s3 should inline y (even though it would normally be too large) because it is only called once
(define p-s3
  `(let ([y (lambda (x) (+ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                           0 (x (lambda (i) i))))])
    (lambda (x) (y x))))

;; p-s4 should inline y no matter the size of the let's body
(define p-s4
  `(lambda (unknown-f)
    (let ([y (lambda (x) (+ 0 (x (lambda (i) i))))])
      (unknown-f
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        (lambda (x) (+ (y x) (y x) (y x) (y x)))))))

;; Should still inline foo, since it removes the binding.
(define p-s5
  `((lambda (x)
     (+ (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
        (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
        (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
        (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
        (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)))
    foo))

;; Should still inline foo, since it will get reduced once inlined.
(define p-s6
  `(let ([foo (lambda (z)
                (lambda (y) (+ 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0
                               y)))])
    ((lambda (x)
      (+ (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
         (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
         (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
         (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)
         (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5) (x 5)))
     (foo 1))))

(define (test-size-bound)
  (set-size-bound! 30)
  (set-effort-bound! 1000000000000000) ;; ignore effort bound for these tests

  (check-equal? (no-change? p-s1) #t)
  (check-equal? (ast-size (optimize-prog p-s2)) 46)
  (check-equal? (smaller? p-s3) #t)
  (check-equal? (larger? p-s4) #t)
  (check-equal? (smaller? p-s5) #t)
  (check-equal? (smaller? p-s6) #t)

  (set-effort-bound! default-effort-bound)
  (set-size-bound! default-size-bound))

(test-size-bound)


















(define t-p11
  `((lambda (x) ((x x) x)) (lambda (y) ((y y) y))))

(define t-p12
  `((lambda (x) (x x)) (lambda (y) ((y y) y))))

(define t-p13
  `((lambda (x) ((x x) x)) (lambda (z) z)))

;; Ideally, this binding would be removed.
(define t-p14
  '(let ([x (lambda (z) z)]) x))

;; x could be propogated the lambda's body, but it would duplicate the work of
;; creating the closure for x 100 times.
(define t-p15
  '(let ([x (lambda (z) z)])
    (let ([f (lambda (y) x)])
      (call-f-100-times f))))

;; f should be folded, but we are not handling mutliple arguments correctly.
(define t-p16
  '(let ([f (lambda (a b) (if a b 5))])
    (f #t (foo 6))))






;; (+ (+ (+ n n) (+ n n)) (+ (+ n n) (+ n n)))
(define p-effort
  `(lambda ()
    (let f (lambda (n) (add1 n))
      (let x (+ (f 5) (f 5) (f 5) (f 5) (f 5))
        (let y (+ (f 5) (f 5) (f 5) (f 5) (f 5))
          (+ x y))))))

(define p-effort2
  `(lambda (a)
    (let g (lambda (k) k)
      (let f (lambda (n)
              (+ (n 5) (n 5) (n 5) (n 5) (n 5) (n 5)))
        (let h (lambda (m)
                 (+ (f m) (f m)))
          (let x (+ (h g) (h g))
            x))))))

(define p-e3
  `(lambda ()
    ((lambda (b) (+ (b 5) (b 5) (b 5) (b 5) (b 5) (b 5)))
     (lambda (c) c))))

(define p-e4
  `(lambda (m)
      (let b (lambda (b) (+ (b) (b)))
        (b (lambda () (b (lambda () (b (lambda () (b (lambda () 6)))))))))))

(define p-e5
  `(lambda (m)
    ((lambda (g)
       (+ (g (lambda (k) k)) (g (lambda (k) (add1 k)))))
     (lambda (f) (+ (f 5) (f 5) (f 5))))))

(define p-e6
  `(let h
    (lambda (m)
        (+ (m (lambda (k) k)) (m (lambda (k) (add1 k)))))
    (let f (lambda (f) (+ (f 5) (f 5) (f 5)))
      (+ (h f) (h f)))))