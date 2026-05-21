#lang racket

(require "parser.rkt")

(provide load-module)

;; Returns a module:
;;   (module <mod-name> <bless> <inline> <blessed> <lets> <defs>)
(define (load-module path)
  (define-values (base-dir _1 _2) (split-path path))
  (define-values (_3 dir-name _4) (split-path (simplify-path base-dir)))
  (define mod-name (path->string dir-name))

  (define ast (strip-prov (parse-file path)))

  (let loop ([ast ast]
             [bless-acc '()]
	           [inline-acc (set)]
             [blessed-acc (set)]
             [let-acc (hash)]
             [def-acc (hash)])
    
    (match ast

      [`(module ,path ,ast)
       (loop ast bless-acc inline-acc blessed-acc let-acc def-acc)]
      
      [`(top-level)
       `(module ,mod-name
                ,(reverse bless-acc)
                ,(set->list inline-acc)
                ,(set->list blessed-acc)
                ,(hash-values let-acc)
                ,(hash->list def-acc))]

      [`(bless ,expr ,rest)
       (loop rest (cons `(bless ,expr) bless-acc) inline-acc blessed-acc let-acc def-acc)]

      [`(blessed ,decl ,(and body `((ref |{}|) . ,_)) ,rest)
       (loop rest 
             bless-acc
	     inline-acc
             (set-add blessed-acc `(blessed ,decl ,body))
             let-acc 
             (for/hash ([(nm lst) (in-hash def-acc)])
		       (values nm (reverse lst))))]

      [`(blessed ,decl ,body ,rest)
       (loop rest 
             bless-acc 
             (set-add inline-acc `(blessed ,decl ,body))
	     blessed-acc
             let-acc 
             (for/hash ([(nm lst) (in-hash def-acc)])
		       (values nm (reverse lst))))]

      [`(def ((ref ,name) ,args ...) ,maybe-when ... ,body ,rest)
       (when (hash-has-key? let-acc name)
         (error (format "Duplicate top-level let binding: ~a" name)))
       (loop rest 
             bless-acc
	     inline-acc
             blessed-acc 
             let-acc 
             (hash-set def-acc name
		       (append (hash-ref def-acc name list)
			       `((def ((ref ,name) ,@args)
				      ,@maybe-when ,body)))))]

      [`(let (ref ,name) ,rhs ,rest)
       (when (or (hash-has-key? let-acc name)
		 (hash-has-key? def-acc name))
         (error (format "Duplicate top-level let binding: ~a" name)))
       (loop rest 
             bless-acc
	     inline-acc
             blessed-acc 
             (hash-set let-acc name `(let (ref ,name) ,rhs)) 
             def-acc)]

      [`(include ,_ ,rest)
       (loop rest bless-acc inline-acc blessed-acc let-acc def-acc)]
     
      [_ (error "Unknown top-level form in module:" ast)])))

