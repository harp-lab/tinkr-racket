#lang racket

(provide inlining-pass)

(define (inlining-pass mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs ,methods ,types)]))