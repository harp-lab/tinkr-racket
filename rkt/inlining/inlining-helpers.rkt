#lang racket

(provide get-effort-bound
         get-size-bound
         set-effort-bound!
         set-size-bound!

         effect-context?
         test-context?
         value-context?
         (struct-out app-context)
         replace-app-context

         start-counters
         try-optimize

         (struct-out environment)
         make-empty-env
         env-has?
         env-ref
         extend-env
         extend-env-circular
         get-env-under-blessed?
         set-env-under-blessed
         get-env-effort
         set-env-effort!
         inc-env-effort!
         get-env-size-total
         set-env-size-total!
         inc-env-size-total!
         get-env-size-delta
         set-env-size-delta!
         inc-env-size-delta!
         inc-size-total!
         accumulate-size-total!
         inc-size-delta!
         accumulate-size-delta!
         abort-inlining-attempt

         (struct-out opnd)
         construct-operand
         construct-operands

         (struct-out var)
         new-variable
         copy-variable
         copy-variables
         variable-set-op

         apply-to-ref-sym)

;; Parameters
(define effort-bound 200)
(define size-bound 30)

(define (get-effort-bound) effort-bound)
(define (get-size-bound) size-bound)
(define (set-effort-bound! v) (set! effort-bound v))
(define (set-size-bound! v) (set! size-bound v))

(struct environment
  [bindings         ;; (HashOf Symbol Var) ;; TODO: is this the right type?
   effort-counter   ;; (or #f (BoxOf Integer))
   size-total       ;; (or #f (BoxOf Integer))
   size-delta       ;; (or #f (BoxOf Integer))
   abort-kont       ;; (or #f Continuation)
   under-blessed?]  ;; Bool
  #:transparent)

;; env can be circular (which is why it's a Box).
(struct opnd
  [exp     ;; Expr
   env     ;; (BoxOf Environment)
   cache]  ;; (BoxOf Expr)
  #:transparent)

(struct var
  [name           ;; Symbol
   op             ;; Opnd
   flags          ;; (MutableSetOf VarFlag)
   source-flags]  ;; (SetOf VarFlag)
  #:transparent)
;; Where VarFlag can be one of 'ref or 'copied

;; A Context is one of 'effect, 'test, 'value, or an AppContext

(struct app-context
  [ops            ;; (ListOf Opnd)
   outer-context  ;; Context
   inlined?]      ;; (BoxOf Bool)
  #:transparent)

(define (effect-context? context) (equal? context 'effect))
(define (test-context? context) (equal? context 'test))
(define (value-context? context) (equal? context 'value))

(define (replace-app-context context replacement)
  (cond
    [(app-context? context) replacement]
    [else context]))

(define (start-counters env do)
  (if (environment-effort-counter env)
      (do env)
      (let/ec kont
        (do (environment
              (environment-bindings env)
              (box 0) ;; Start effort counter
              #f      ;; Do not start total size counter
              (box 0) ;; Start delta size counter
              kont
              (environment-under-blessed? env))))))

;; A helper to try optimizing (this will start the counters) or otherwise fail.
(define (try-optimize env do-try do-fail)
  (define tried-value
    (start-counters env do-try))

  (if tried-value
      tried-value
      (do-fail)))

(define (make-empty-env)
  (environment (hash) #f #f #f #f #f))

(define (env-has? env x)
  (hash-has-key? (environment-bindings env) (var-name x)))

(define (env-ref env x)
  (hash-ref (environment-bindings env) (var-name x)))

(define (extend-env env xs xs^)
  (define bindings
    (for/fold ([bindings (environment-bindings env)])
              ([x xs]
               [x^ xs^])
      (hash-set bindings (var-name x) x^)))

  (environment
    bindings
    (environment-effort-counter env)
    (environment-size-total env)
    (environment-size-delta env)
    (environment-abort-kont env)
    (environment-under-blessed? env)))

(define (extend-env-circular env xs xs^)
  (define bindings
    (for/fold ([bindings (environment-bindings env)])
              ([x xs]
               [x^ xs^])
      (hash-set bindings (var-name x) x^)))

  (define env^
    (environment
      bindings
      (environment-effort-counter env)
      (environment-size-total env)
      (environment-size-delta env)
      (environment-abort-kont env)
      (environment-under-blessed? env)))

  ;; Make the environment circular
  (for ([x^ xs^])
    (define x^-env-box (opnd-env (var-op x^)))
    (define x^-env (unbox x^-env-box))
    (set-box!
      x^-env-box
      (environment
        bindings
        (environment-effort-counter env)
        (environment-size-total x^-env)
        (environment-size-delta env)
        (environment-abort-kont env)
        (environment-under-blessed? env))))

  env^)

(define (get-env-under-blessed? env)
  (environment-under-blessed? env))

(define (set-env-under-blessed env under-blessed?)
  (environment
    (environment-bindings env)
    (environment-effort-counter env)
    (environment-size-total env)
    (environment-size-delta env)
    (environment-abort-kont env)
    under-blessed?))

(define (get-env-effort env)
  (if (environment-effort-counter env)
      (unbox (environment-effort-counter env))
      #f))
(define (set-env-effort! env effort)
  (when (environment-effort-counter env)
        (set-box! (environment-effort-counter env) effort)))
(define (inc-env-effort! env)
  (define effort (get-env-effort env))
  (if effort
      (set-env-effort! env (add1 effort))
      env))

(define (get-env-size-total env)
  (if (environment-size-total env)
      (unbox (environment-size-total env))
      #f))
(define (set-env-size-total! env size)
  (when (environment-size-total env)
        (set-box! (environment-size-total env) size)))
(define (inc-env-size-total! env)
  (define size (get-env-size-total env))
  (if size
      (set-env-size-total! env (add1 size))
      env))

(define (get-env-size-delta env)
  (if (environment-size-delta env)
      (unbox (environment-size-delta env))
      #f))
(define (set-env-size-delta! env size)
  (when (environment-size-delta env)
        (set-box! (environment-size-delta env) size)))
(define (inc-env-size-delta! env)
  (define size (get-env-size-delta env))
  (if size
      (set-env-size-delta! env (add1 size))
      env))

(define (inc-size-total! env)
  (accumulate-size-total! env 1))
(define (accumulate-size-total! env add-size)
  (define size (get-env-size-total env))
  (when size
    (set-env-size-total! env (+ size add-size))))

(define (inc-size-delta! env)
  (define size (get-env-size-delta env))
  (when size
    (if (< size size-bound)
        (inc-env-size-delta! env)
        (abort-inlining-attempt env))))
(define (accumulate-size-delta! env add-size)
  (define size (get-env-size-delta env))
  (when (and size (not (< (+ size add-size) size-bound)))
    (displayln (format "aborting because of size: size = ~a, add-size = ~a" size add-size)))
  (when size
    (if (< (+ size add-size) size-bound)
        (set-env-size-delta! env (+ size add-size))
        (abort-inlining-attempt env))))

(define (abort-inlining-attempt env)
  (displayln "ABORTING INLINING ATTEMPT")
  ((environment-abort-kont env) #f))

(define (construct-operand expr env)
  (define env^
          (environment (environment-bindings env)
                        (environment-effort-counter env)
                        (box 0) ;; Different total size counter for each operand
                        (environment-size-delta env)
                        (environment-abort-kont env)
                        (environment-under-blessed? env)))

  (opnd expr (box env^) (box #f)))

(define (construct-operands exprs env)
  (map (lambda (e) (construct-operand e env)) exprs))

;; Symbol -> Var
(define (new-variable x-sym)
  (var x-sym '() (mutable-set) (set)))

;; Var -> Var
(define (copy-variable x)
  (match-define (var x-sym op flags source-flags) x)
  (define x^ (var (gensym x-sym) op (mutable-set) flags))
  x^)

;; (ListOf Var) -> (ListOf Var)
(define (copy-variables xs)
  (map copy-variable xs))

;; Var Opnd -> Var
(define (variable-set-op x op)
  (match-define (var x-sym _ flags source-flags) x)
  (var x-sym op flags source-flags))

(define (apply-to-ref-sym ref f)
  (match ref
    [`(ref ,x) `(ref ,(f x))]
    [`(|...| (ref ,x)) `(|...| (ref ,(f x)))]))
