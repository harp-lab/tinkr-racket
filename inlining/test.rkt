#lang racket

(require rackunit "inlining.rkt")

(define (alpha-equiv? p0 p1)
  (equal? (alphatize p0) (alphatize p1)))

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

(check-equal? (alpha-equiv? (optimize-prog p8) p8) #t)

;; TODO: letrec
(define p10
  `(letrec fact (lambda (n)
                  (if (< n 2)
                      1
                      (* n (fact (- n 1)))))
    (fact 5)))

(define p11
  `((lambda (x) ((x x) x)) (lambda (y) ((y y) y))))

(define p12
  `((lambda (x) (x x)) (lambda (y) ((y y) y))))

(define p13
  `((lambda (x) ((x x) x)) (lambda (z) z)))

(define p14
  '(let x (lambda (z) z) x))

(define p-alpha
  `(let x 0
    (let f (lambda (x)
              (let g (lambda (x) x)
                (g (add1 x))))
      (f 9))))

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

;; 8 calls to f
(define p-e7
  `(let f (lambda (f) (+ (f 5) (f 5) (f 5)))
    (let g1
      (lambda (g1)
        (let g2
          (lambda (g2)
            (+ (g2 (lambda (k) k)) (g2 (lambda (k) (add1 k)))))
          (+ (g2 g1) (g2 g1))))
      (+ (g1 f) (g1 f)))))

;; Should be 128 calls to f
(define p-e8
  `(let f (lambda (f) (+ (f 5) (f 5) (f 5)))
    (let g1
      (lambda (g1)
        (let g2
          (lambda (g2)
            (let g3
              (lambda (g3)
                (let g4
                  (lambda (g4)
                    (let g5
                      (lambda (g5)
                        (let g6
                          (lambda (g6)
                            (+ (g6 (lambda (k) k)) (g6 (lambda (k) k))))
                          (+ (g6 g5) (g6 g5))))
                      (+ (g5 g4) (g5 g4))))
                  (+ (g4 g3) (g4 g3))))
              (+ (g3 g2) (g3 g2))))
          (+ (g2 g1) (g2 g1))))
      (+ (g1 f) (g1 f)))))

