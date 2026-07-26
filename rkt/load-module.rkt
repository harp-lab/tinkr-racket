#lang racket

(require "parser.rkt")

(provide load-module)

;; --- Qualified references: include "m.ti" [as m] enables m.x ---

;; Collects [as <alias>] clauses from this module's .ti includes.
;; Returns alias-symbol -> include-path-string.
(define (collect-aliases ast path)
  (define aliases (make-hash))
  (let walk ([e ast])
    (match e
      [`(include (const ,p) ,cls ... ,body)
       (for ([c (in-list cls)])
         (match c
           [`(clause as ,m)
            (unless (and (string? p) (string-suffix? p ".ti"))
              (error (format "load error in ~a: [as ~a] is only meaningful on a .ti module include, but appears on include \"~a\"" path m p)))
            (when (hash-has-key? aliases m)
              (error (format "load error in ~a: duplicate module alias '~a' — [as ~a] appears on more than one include" path m m)))
            (hash-set! aliases m p)]
           [`(clause as ,_ ...)
            (error (format "load error in ~a: malformed [as ...] clause on include \"~a\" — expected exactly one alias name, e.g. [as m]" path p))]
           [_ (void)]))
       (walk body)]
      [(? list? l) (for-each walk l)]
      [_ (void)]))
  aliases)

;; Rewrites alias-qualified references m.x into single free names |m.x|.
;; These flow through the whole pipeline as ordinary global refs; since
;; identifiers cannot contain dots, they can never collide with user names,
;; and escape-id-for-C renders the dot as the unforgeable marker _0002e
;; that the linker splits back apart.
(define (rewrite-qualified ast aliases path)
  (let Q ([e ast])
    (match e
      [`((ref ,d) ,lhs ,rhs)
       #:when (eq? d '|.|)
       (match* (lhs rhs)
         [(`(ref ,m) `(ref ,x))
          (unless (hash-has-key? aliases m)
            (error (format "load error in ~a: unknown module alias '~a' in qualified reference ~a.~a — aliases in scope: ~a. Add [as ~a] to the intended include."
                           path m m x
                           (if (hash-empty? aliases)
                               "(none)"
                               (string-join (map symbol->string (hash-keys aliases)) ", "))
                           m)))
          `(ref ,(string->symbol (format "~a.~a" m x)))]
         [(_ _)
          (error (format "load error in ~a: a qualified reference must have the form <alias>.<name>; '.' was applied to ~v and ~v" path lhs rhs))])]
      [(? list? l) (map Q l)]
      [_ e])))

;; Returns a module:
;;   (module <mod-name> <bless> <inline> <blessed> <lets> <defs>)
(define (load-module path)
  (define-values (base-dir _1 _2) (split-path path))
  (define-values (_3 dir-name _4) (split-path (simplify-path base-dir)))
  (define mod-name (path->string dir-name))

  (define ast0 (strip-prov (parse-file path)))
  (define aliases (collect-aliases ast0 path))
  (define ast (rewrite-qualified ast0 aliases path))

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

