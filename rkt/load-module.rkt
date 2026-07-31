#lang racket

(require "parser.rkt")

(provide load-module)

;; --- Qualified references: include "m.ti" [as m] enables m.x ---

;; Folds a left-nested chain of '.' applications of bare refs into one
;; dotted name string: ((a.b).c) -> "a.b.c". Any other '.' shape is #f.
(define (dot-chain->name e)
  (match e
    [`(ref ,x) (and (symbol? x) (symbol->string x))]
    [`((ref ,d) ,lhs ,rhs)
     #:when (eq? d '|.|)
     (define l (dot-chain->name lhs))
     (define r (dot-chain->name rhs))
     (and l r (string-append l "." r))]
    [_ #f]))

;; Rewrites alias-qualified references m.x (or m.n.x ...) into single free
;; names |m.x|. These flow through the whole pipeline as ordinary global
;; refs; since identifiers cannot contain dots, they can never collide with
;; user names, and escape-id-for-C renders the dot as the unforgeable marker
;; _0002e that the linker splits back apart. Whether a dotted name resolves
;; is decided at link time (aliases may arrive through transitive includes).
(define (rewrite-qualified ast path)
  (let Q ([e ast])
    (match e
      [`((ref ,d) ,lhs ,rhs)
       #:when (eq? d '|.|)
       (define name (dot-chain->name e))
       (unless name
         (error (format "load error in ~a: a qualified reference must have the form <alias>.<name> (aliases may nest: a.b.x); '.' was applied to ~v and ~v" path lhs rhs)))
       `(ref ,(string->symbol name))]
      [(? list? l) (map Q l)]
      [_ e])))

;; Returns a module:
;;   (module <mod-name> <bless> <inline> <blessed> <lets> <defs>)
(define (load-module path)
  (define-values (base-dir _1 _2) (split-path path))
  (define-values (_3 dir-name _4) (split-path (simplify-path base-dir)))
  (define mod-name (path->string dir-name))

  (define ast (rewrite-qualified (strip-prov (parse-file path)) path))

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

      ;; Includes may carry clause forms: (include <path> (clause ...) ... <rest>)
      [`(include ,_ ... ,rest)
       (loop rest bless-acc inline-acc blessed-acc let-acc def-acc)]
     
      [_ (error "Unknown top-level form in module:" ast)])))

