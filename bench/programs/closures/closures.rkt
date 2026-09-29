#lang racket/base

(define ((compose f g) x) (f (g x)))
(define ((make-adder n) x) (+ x n))

(define (loop n acc)
  (if (= n 0)
      acc
      (let ([f (compose (make-adder 1) (make-adder n))])
        (loop (- n 1) (f acc)))))

(displayln (loop 1000000 0))
