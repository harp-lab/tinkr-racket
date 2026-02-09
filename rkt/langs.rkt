#lang racket


(provide sm-core-ir?
	 valid-const?)


(require "utils.rkt")


(define (ref? a)
  (match a [`(ref ,(? symbol?)) #t] [_ #f]))

(define (atom? a)
  (match a [(? ref?) #t] [`(const ,(? (not/c list?))) #t] [_ #f]))

(define (t-atom? a)
  (match a
    [(? atom?) #t]
    [`((ref ,ell) ,(? ref?)) #:when (eq? ell '|...|) #t]
    [`(,ell ,(? ref?)) #:when (eq? ell '|...|) #t]
    [_ #f]))

(define (params? a)
  (match a [`(,(? atom?) ... ,(? t-atom?)) #t] [_ #f]))

(define (valid-const? v)
  (or (integer? v) (string? v) (symbol? v)))

(define (blessed? e) 'todo #t)

(define (sm-core-ir? ast)
  
  (define (ref? x)
    (match x [`(ref ,s) (symbol? s)] [_ #f]))

  (define (expr? e)
    (match e
      [(? t-atom?) #t]
      
      [`(bless ,(? blessed?)) #t]
      
      [`(let ,(? ref?) ,val ,body)
       (and (expr? val) (expr? body))]
      
      [`(if ,(? expr?) ,(? expr?) ,(? expr?)) #t]
      
      [`(lambda ,(? params?) ,(? expr?)) #t]
      
      [`(,(or 'object 'subword 'fixed-alloc) ,es ...)
       (and (andmap expr? es))]
      
      [`((ref ,ell) ,sub) #:when (eq? ell '|...|) (expr? sub)]
      
      [`(,f ,args ...)
       (and (expr? f) (andmap expr? args))]
      
      [_ #f]))

  (match ast
    [`(let ,(? ref?) ,(? expr? val)) #t]
    
    [`(def ,(? params?) ,(? expr?)) #t]
    
    [`(blessed ,(? params?) ,(? expr?)) #t]
    
    [_ (pretty-print ast) (display (print-ast ast)) #f]))

