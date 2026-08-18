#lang racket

(require "helpers.rkt")

(provide annotate-well-known)

;; AnnotatedFreeVarsMod -> AnnotatedWellKnownModule
(define (annotate-well-known mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (define annotated-defs (map annotate-well-known/def defs))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,annotated-defs ,methods ,types)]))

;; Expr -> (ValuesOf Expr (SetOf Symbol))
;; Walk the ast and add well-known annotations to inner defs and
;; return set of (fully) well-known names.
(define (annotate-well-known/def def-ast)
  (match def-ast
    [`(def (,xs ...) ,annotations ,body)
      (define-values (body+ well-known-names) (annotate-well-known/ast body (set)))
      `(def (,@xs) ,annotations ,body+)]
    [_ (error 'annotate-well-known)]))

;; Expr (SetOf Symbol) -> (ValuesOf Expr (SetOf Symbol))
(define (annotate-well-known/ast ast names)
 (define (recur ast outer-expr)
    (define-values (expr well-known-names) (annotate-well-known/ast ast names))
    (values
      (outer-expr expr)
      well-known-names))

  (define (recur-exprs asts outer-expr)
    (cond 
      [(null? asts) (values (outer-expr '()) names)]
      [else
        (define-values (exprs well-known-names)
          (for/foldr ([exprs (list)]
                      [well-known-names #f])
                     ([ast asts])
            (define-values (expr new-well-known-names) (annotate-well-known/ast ast names))
            
            (values
              (cons expr exprs)
              (if well-known-names
                  (set-intersect well-known-names new-well-known-names)
                  new-well-known-names))))

        (values
          (outer-expr exprs)
          well-known-names)]))

  (match ast
    [`(ref ,x) (values `(ref ,x) (set-remove names x))]
    [`(const ,_) (values ast names)]
    
    ;; Bless
    [`(bless ,e0)
      (recur e0 (lambda (e0) `(bless ,e0)))]

    [`(if ,g ,t ,e)
      (recur-exprs (list g t e) (lambda (es) `(if ,@es)))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail) (values ast names)]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (recur e0 (lambda (e0) `(,ell ,e0)))]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-exprs es (lambda (es) `(,ctor ,@es)))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (define-values (rhs+ rhs-well-known) (annotate-well-known/ast rhs names))
      (define-values (body+ body-well-known) (annotate-well-known/ast body names))

      (values
        `(let (ref ,x) ,rhs+ ,body+)
        (set-intersect rhs-well-known body-well-known))]

    [`(|[]| ,es ...)
      (recur-exprs es (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def (,xs ...) ,annotations ,body ,more)
      (annotate-well-known/inner-def ast names)]

    ;; Well-known call site
    [`((ref ,fx) ,es ...)
     #:when (set-member? names fx)
     (recur-exprs es (lambda (es) `((ref ,fx) ,@es)))]
    
    ;; Remaining untagged applications
    [`(,es ...)
     (recur-exprs es (lambda (es) `(,@es)))]))

;; Expr (SetOf Symbol) -> (ValuesOf Expr (SetOf Symbol))
(define (annotate-well-known/inner-def ast names)
  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-nested-sibling-defs ast))

  ;; Extract fail chains:

  ;; (SetOf (ListOf Symbol))
  (define fail-chains (get-fail-chains defs))

  ;; (ListOf (ListOf Expr))
  ;; Get the whole expr instead of just the names
  (define chains
    (set-map fail-chains 
             (lambda (def-names)
              (map (lambda (def-name)
                      (get-def-with-name defs def-name))
                    def-names))))

  ;; Retrieve first def names in order to pass to recursive calls
  (define def-names
    (for/set ([chain-names fail-chains])
      (car chain-names)))

  (define new-names (set-union names def-names))

  ;; Recur on the chains
  (define-values (chains+ well-known-for-defs) (annotate-well-known/def-chains chains new-names))
  
  ;; Recur on the rest-ast
  (define-values (rest-ast+ well-known-rest-ast) (annotate-well-known/ast rest-ast new-names))

  ;; Names that are well-known to all the sibling defs and the rest-ast
  (define well-known-total (set-intersect well-known-for-defs well-known-rest-ast))
  
  ;; Add is_well_known annotations to first defs and flatten
  (define defs+
    (foldr append '()
      (for/list ([chain (in-list chains+)])
        (define first-def (car chain))
        (define first-def+
          (match first-def
            [`(def ((ref ,fx) ,params ...) ,annotations ,body)
              (define is-well-known? (set-member? well-known-total fx))
              
              (define annotations+
                (if is-well-known?
                    (cons `(is_well_known) annotations) ;; Annotate as well known
                    annotations))

            `(def ((ref ,fx) ,@params) ,annotations+ ,body)]))
        
        (cons first-def+ (cdr chain)))))
  
  (values
    (nest-sibling-defs defs+ rest-ast+) ; Splice defs back together
    well-known-total))

;; A Chain is a (ListOf (ListOf Expr))
;; Chain (SetOf Symbol) -> (ValuesOf Chain (SetOf Symbol))
;; Recur on the bodies and add well_known annotations (but not is_well_known annotations) to each def
(define (annotate-well-known/def-chains chains names)
  (for/fold ([chains+ (list)]
             [well-known-total #f]) ;; Default to #f (instead of (set)) since we don't want to intersect with (set)
            ([chain (in-list chains)])
    (define-values (chain+ well-known-for-group)
      (for/fold ([defs (list)]
                 [well-known-for-group #f])
                ([def (in-list chain)])
        (match def
          [`(def (,xs ...) ,(list-no-order `(free_vars ,(and free-refs `(ref ,free)) ...) other ...) ,body)
            (define-values (body+ well-known-body) (annotate-well-known/ast body names))

            ;; Well-known names actually referenced in the body (names not referenced in body are concidered well-known)
            (define well-known-used-in-body (set-intersect well-known-body (list->set free)))
            (define well-known-refs (map add-ref (set->list well-known-used-in-body)))

            (values
              (append
                defs
                (list `(def (,@xs) ((well_known ,@well-known-refs) (free_vars ,@free-refs) ,@other) ,body+)))
              (if well-known-for-group
                  (set-intersect well-known-for-group well-known-body)
                  well-known-body))])))
    
    (values
      (cons chain+ chains+)
      (if well-known-total
          (set-intersect well-known-total well-known-for-group)
          well-known-for-group))))