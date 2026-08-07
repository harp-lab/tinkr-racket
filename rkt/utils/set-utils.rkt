#lang racket

(provide set-filter)

;; Fun Set -> Set
(define (set-filter f st)
  (for/set ([elm (in-set st)] 
            #:when (f elm))
    elm))