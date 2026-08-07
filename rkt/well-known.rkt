#lang racket

(require "utils/utils.rkt"
         "simplify.rkt"
         "helpers.rkt")

(provide lift-well-known-defs)


(struct chain
  [defs         ;; (ListOf Expr)
    free-vars    ;; (CollectionOf Symbol)
    well-known]  ;; (SetOf Symbol)
  #:transparent)

;; (CollectionOf Chain) -> (ListOf Expr)
(define (flatten-chains chains)
  (foldl append '()
          (for/list ([chain chains])
            (chain-defs chain))))

;; An Env is a (HashOf Symbol (ListOf Symbol))

;; AnnotatedWellKnownMod -> WellKnownModule
(define (lift-well-known-defs mod)
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)

     (define defs+
       (foldr append '() ;; flatten one level
        (for/list ([ast defs]) 
          (set->list (lift-well-known/def ast)))))

     `(module ,name ,mtag ,bless ,inline ,blessed
	      ,lets ,defs+ ,methods ,types)]))

;; Expr -> (SetOf Expr)
(define (lift-well-known/def def-ast)
  (match def-ast
    [`(def (,xs ...) ,annotations ,body)
      (define-values (new-body new-defs) (lift-well-known/ast body (hash)))
      (set-add new-defs `(def (,@xs) ,annotations ,new-body))]
    [_ (error 'lift-well-known-defs)]))

;; Expr Env -> (ValuesOf Expr (SetOf Expr))
;; Lifts well-known defs from the expression to the top level while using an
;; environment mapping well-known def names to the free variables it needs
;; (in order to transform later call-sites).
;; Returns the modified expression and a list of top-level defs which are being lifted out.
(define (lift-well-known/ast ast env)
  (define (recur-exprs asts outer-expr)
    (define-values (exprs defs)
      (for/foldr ([exprs (list)]
                  [defs (set)])
                 ([ast asts])
        (define-values (expr new-defs) (lift-well-known/ast ast env))
        
        (values
          (cons expr exprs)
          (set-union defs new-defs))))

    (values
      (outer-expr exprs)
      defs))

  (match ast
    [`(ref ,x)
      (values `(ref ,x) (set))]

    ;; No change to constants
    [`(const ,_) (values ast (set))]
    
    ;; Bless
    [`(bless ,e0)
      (values ast (set))]

    ;; Simple recursion
    [`(if ,g ,t ,e)
      (define-values (g-expr g-defs) (lift-well-known/ast g env))
      (define-values (e-expr e-defs) (lift-well-known/ast t env))
      (define-values (t-expr t-defs) (lift-well-known/ast e env))

      (values
        `(if ,g-expr ,e-expr ,t-expr)
        (set-union g-defs e-defs t-defs))]

    [`(continue-dispatch ,es ...)
      (recur-exprs es
                   (lambda (es) `(continue-dispatch ,@es)))]
    
    [`(fail)
     (values `(fail) (set))]

    [`(,ell ,e0) #:when (eq? ell '|...|)
      (define-values (expr defs) (lift-well-known/ast e0 env))

      (values
        `(,ell ,expr)
        defs)]
    
    [`(,(and ctor (or 'object 'subword)) ,es ...)
      (recur-exprs es
                   (lambda (es) `(,ctor ,@es)))]

    ;; Let
    [`(let (ref ,x) ,rhs ,body)
      (define-values (rhs-expr rhs-defs) (lift-well-known/ast rhs env))
      (define-values (body-expr body-defs) (lift-well-known/ast body env))

      (values
        `(let (ref ,x) ,rhs-expr
              ,body-expr)
        (set-union rhs-defs body-defs))]

    ;; Slices
    [`(|[]| ,es ...)
      (recur-exprs es
                   (lambda (es) `(|[]| ,@es)))]

    ;; Inner def
    [`(def ((ref ,fx) ,xs ...) ,annotations ,body ,more)
      (lift-well-known/inner-def ast env)]

    ;; Well-known call sites
    [`((ref ,fx) ,fallback ,arg-count ,es ...)
      (define-values (new-es es-defs) (recur-exprs es (lambda (es) es)))

      (define free-vars (hash-ref env fx (list)))
      (define free-refs (map add-ref free-vars))

      (values
        `((ref ,fx) ,fallback ,arg-count ,@free-refs ,@new-es)
        es-defs)]

    ;; Untagged application
    [`(,fe ,fallback ,arg-count ,es ...)
      (define-values (fe-expr fe-defs) (lift-well-known/ast fe env))
      (define-values (new-es es-defs) (recur-exprs es (lambda (es) es)))

      (values
        `(,fe-expr ,fallback ,arg-count ,@new-es)
        (set-union fe-defs es-defs))]))


;; Expr Env -> (ValuesOf Expr (SetOf Expr))
(define (lift-well-known/inner-def def-ast env)
  ;; Unnest the nested sibling defs
  (define-values (defs rest-ast) (get-nested-sibling-defs def-ast))

  ;; Extract fail chains in order to know what is the first def in the chain to test if it
  ;; is well-known and, if it is well-known, pass along all free variables for the entire chain.
  (define fail-chains (get-fail-chains defs))

  ;; Combine free vars for each fail chain (and construct chain structures)
  (define chains
    (for/set ([chain-names fail-chains])
      (for/fold ([def-chain (chain (list) (set) (set))])
                ([def-name chain-names])

          (define def (get-def-with-name defs def-name))
          
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,(and params (or `(ref ,xs)
                                                                                    `(|...| (ref ,xs)))) ...)
                ,(and annotations (list-no-order `(free_vars (ref ,free-vars) ...) `(well_known (ref ,well-known-def-calls) ...) other ...))
                ,body)

              ;; Extra free vars that are being added in this pass which need to be passed to
              ;; well known call sites (and thus need to be threaded through this def).
              (define free-vars-from-calls
                (for/fold ([free-vars-from-calls (set)])
                          ([name well-known-def-calls])
                  (define free-vars-for-call (hash-ref env name (list)))
                  (set-union free-vars-from-calls (list->set free-vars-for-call))))

              ;; These def names are being moved to the top level, so they can
              ;; be safely removed from the free vars
              (define lifted-defs-to-remove (list->set (hash-keys env)))

              (define total-free-vars
                (set-subtract
                  (set-union (list->set free-vars) (chain-free-vars def-chain) free-vars-from-calls)
                  lifted-defs-to-remove))

              (define def+
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,(remove-annotation annotations 'well_known) ,body))

              (chain (append (chain-defs def-chain) (list def+))
                     total-free-vars
                     (set-union (chain-well-known def-chain) (list->set well-known-def-calls)))]))))

  ;; Determine whether def chains are well-known
  (define well-known-chains
    (for/fold ([well-known-chains (set)])
              ([curr-chain (in-set chains)])
      (define first-def (car (chain-defs curr-chain)))

      (if (annotation-exists-on-def? first-def 'is_well_known)
          (set-add well-known-chains curr-chain)
          well-known-chains)))

  (define well-known-def-names
    (get-def-names (flatten-chains well-known-chains)))

  ;; Handle flow of free vars between well-known sibling calls
  (define well-known-chains+ (pass-free-vars-through-mutual-calls well-known-chains))

  ;; Lift well-known def groups
  (define lifted-chains
    (for/set ([curr-chain (in-set well-known-chains+)])
              
      ;; pick an arbitrary ordering for the free vars
      (define group-free-vars (set->list (set-subtract (chain-free-vars curr-chain) well-known-def-names)))
      (define group-free-var-refs (map (lambda (x) `(ref ,x)) group-free-vars))

      (define new-lifted-defs
        (for/list ([def (chain-defs curr-chain)])
          (match def
            [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,annotations ,body)

              (define new-lifted-def
                `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@group-free-var-refs ,@params) ,annotations ,body))

              new-lifted-def])))

      (chain new-lifted-defs group-free-vars (set))))

  (define lifted-defs (flatten-chains lifted-chains))

  ;; Modify the environment to include the new well-known defs' free vars
  (define env+
    (for/fold ([env+ env])
              ([group (in-set lifted-chains)])
      (define first-def-name (get-def-name (car (chain-defs group))))

      (hash-set env+ first-def-name (chain-free-vars group))))

  ;; Lift well-known defs from newly lifted defs bodies
  (define-values (lifted-defs+ lifted-defs-from-wk-defs) (lift-well-known/inner-def-bodies lifted-defs env+))
  (define lifted-defs-final
    (for/list ([lifted-def (in-list lifted-defs+)]) ;; Remove the is_well_known annotation: we don't need it anymore
        (remove-annotation-on-def lifted-def 'is_well_known)))

  ;; Lift well-known defs from bodies of non-well-known-defs
  (define non-well-known-chains (set-subtract chains well-known-chains))
  (define non-well-known-defs (flatten-chains non-well-known-chains))
  (define-values (non-well-known-defs+ lifted-defs-from-non-wk-defs) (lift-well-known/inner-def-bodies non-well-known-defs env+))

  ;; Lift well-known defs from rest-ast
  (define-values (rest-expr+ new-defs-from-rest) (lift-well-known/ast rest-ast env+))

  (add-to-global-names! well-known-def-names)

  (values
    (nest-sibling-defs non-well-known-defs+ rest-expr+)
    (set-union (list->set lifted-defs-final) lifted-defs-from-wk-defs lifted-defs-from-non-wk-defs new-defs-from-rest)))

;; (ListOf Expr) Env -> (ValuesOf (ListOf Expr) (SetOf Expr))
(define (lift-well-known/inner-def-bodies defs env)
  (for/fold ([defs+ (list)]
             [lifted-defs (set)])
            ([def (in-list defs)])
    (match def
      [`(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,params ...) ,annotations ,body)
        (define-values (new-body new-defs) (lift-well-known/ast body env))

        (values
          (append
            defs+
            (list `(def ((ref ,fx) (ref ,fallback-x) (ref ,arg-count-x) ,@params) ,annotations ,new-body)))
          (set-union new-defs lifted-defs))])))


;; (SetOf Chain) -> (SetOf Chain)
(define (pass-free-vars-through-mutual-calls well-known-chains)
  (define def-name->free-vars
    (for/hash ([group (in-set well-known-chains)])
      (define first-def-name (get-def-name (car (chain-defs group))))
      (values first-def-name (chain-free-vars group))))

  (define well-known-first-def-names
    (get-def-names
      (set-map well-known-chains (lambda (g) (car (chain-defs g))))))

  ;; Adjacency list/hash representation of call graph
  (define sibling-calls-graph
    (for/hash ([group (in-set well-known-chains)])
      (define first-def-name (get-def-name (car (chain-defs group))))

      ;; filter out any non-sibling calls
      (define sibling-calls (set-filter (lambda (name) (set-member? well-known-first-def-names name))
                                        (chain-well-known group)))

      (values first-def-name sibling-calls)))

  (define reachability-graph (transitive-closure sibling-calls-graph))

  ;; Add the free vars of reachable well-known sibling calls to the chain's free vars
  (for/set ([group (in-set well-known-chains)])
    (define first-def-name (get-def-name (car (chain-defs group))))
    (define reachable-calls (hash-ref reachability-graph first-def-name (set)))
    (define reachable-calls-fvs
      (foldl set-union (set)
        (for/list ([call-name reachable-calls])
          (hash-ref def-name->free-vars call-name (set)))))
    
    (chain (chain-defs group)
                (set-union (chain-free-vars group) reachable-calls-fvs)
                (chain-well-known group))))

;; (HashOf Symbol (SetOf Symbol)) -> (HashOf Symbol (SetOf Symbol))
;; A naive implementation of finding the transitive closure of a graph.
(define (transitive-closure graph)
  (define (fixpoint graph previous)
    (if (equal? graph previous)
        graph
        (fixpoint (reachable-step graph) graph)))

  (fixpoint graph (hash)))

(define (reachable-step graph)
  (for/hash ([(h reachable-set) (in-hash graph)])
    (define reachable-set+
      (foldl set-union reachable-set
        (for/list ([n (in-set reachable-set)])
          (hash-ref graph n))))

    (values h reachable-set+)))