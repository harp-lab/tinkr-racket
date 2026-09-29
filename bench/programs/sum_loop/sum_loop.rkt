#lang racket/base

(define (loop n acc)
  (if (= n 0)
      acc
      (loop (- n 1) (+ acc n))))

(displayln (loop 3000000 0))
