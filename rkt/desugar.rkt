#lang racket

(require "utils.rkt"
         "langs.rkt")

(provide desugar-module)

;; Returns a desugared module:
;;   (module <mod-name> <mod-tag> 
;;           <bless> <all-inline> <blessed> <lets> <defs>
;;           <methods> <types>)
(define (desugar-module mod)
  ;; Method registry for this module
  (define method-map (hash))
  (define (register-method! name obj name+)
    (set! method-map (hash-set method-map (cons name obj) name+)))

  (define types-st (set))
  (define (register-type! tag) (set! types-st (set-add types-st tag)) tag)
  
  (define fallback-x (gensymb 'fallback))

  (define special '(_slice _fun_ptr _subword)) ;; TODO: do we need _fun_ptr anymore?
  (define this-mod-tag (gensymb (gensymb 'm))) 
  (define this-mod-tag-str (symbol->string this-mod-tag))
  (define (private-obj-tag tag) ;; makes tag unique to module
    (register-type!
     (sym-append tag (if (member tag special) "" this-mod-tag-str))))
  (define (private-subword-tag tag) ;; makes tag unique to module
    (register-type!
     (sym-append tag (if (member tag special) ""
			 (string-append this-mod-tag-str "subword")))))

  (define (method-publish-name mname otag)
    (sym-append mname (sym-append "_" otag)))

  ;; Lifted and new defs
  (define lifted-defs (make-hash))
  (define (lift-def! name ast)
    (hash-set! lifted-defs name ast))

  ;; Expr Expr -> Expr
  ;; For debuging purposes.
  (define (with-print-debug-desguared val-ast ast)
    `((ref |;|) (ref none)
          ((ref debug_print) (ref none) ((ref write) (ref none) ,val-ast))
          ,ast))
  (define (with-print-debug val-ast ast)
    `((ref |;|)
          ((ref debug_print) ((ref write) ,val-ast))
          ,ast))

  ;; Expr -> (SetOf Symbol)
  (define (gather-pattern-variables pat [qd 0])
    (define (recur-pats pats)
      (foldl (lambda (p st) (set-union st (gather-pattern-variables p qd))) (set) pats))

    (match pat
      ;; Quotes
      [`((ref |`|) ,pat0)
       (gather-pattern-variables pat0 (+ qd 1))]
      [`((ref |,|) ,pat0) #:when (= qd 0)
       (set)]
      [`((ref |,|) ,pat0)
       (gather-pattern-variables pat0 (- qd 1))]
      
      ;; Constants
      [`(const ,v)
       (set)]

      ;; ref pattern qd>0 
      [`(ref ,x) #:when (> qd 0)
       (set)]

      ;; ref pattern qd=0
      [`(ref _) #:when (= qd 0) (set)]
      [`(ref ,x) #:when (= qd 0)
       (set x)]

      ;; = and &
      [`((ref =) (ref ,px) ,pats ...)
       (set-add (recur-pats pats) px)] ;; TODO: disallow/allow other pvs other than px?
      [`((ref |&|) ,pats ...)
        (recur-pats pats)]
      
      ;; Subwords
      [`((ref |[]|) ((ref |[]|) (ref ,tag) ,pat0))
        (gather-pattern-variables pat0 qd)]

      ;; _slice
      [`((ref |[]|) (ref _slice) ,pat0)
        (gather-pattern-variables pat0 qd)]

      ;; Objects
      [`((ref |[]|) (ref ,tag) ,pats ...)
       #:when (and (> qd 0) (symbol? tag))
        (recur-pats pats)]
      
      ;; Slices
      [`((ref |[]|) ,pats ...)
        (recur-pats pats)]
      
      ;; ? patterns
      [`((ref |?|) (ref ,px) (ref ,pred))
       (set px)]

      ;; ... patterns
      [`((ref ,ell) ,pat0) #:when (eq? ell '|...|)
        (gather-pattern-variables pat0 qd)]
      
      [_
        (displayln (format "gather-pattern-variables failed for pattern: ~a" pat))
        (error 'gather-pattern-variables-error)]))

  ;; Symbol (ListOf Symbol) Expr -> Expr
  (define (unpack-accs accs-x pvs body)
    (match pvs
      ['() body]
      [`(,a)
        `(let (ref ,a) ((ref first) (ref none) (ref ,accs-x))
           ,body)]
      [`(,a . ,b)
        `(let (ref ,a) ((ref first) (ref none) (ref ,accs-x))
          (let (ref ,accs-x) ((ref rest) (ref none) (ref ,accs-x))
            ,(unpack-accs accs-x b body)))]))

  ;; Expr (HashOf Symbol Symbol) -> Expr
  (define (rename-pattern-variables pat renaming [qd 0])
    (define (recur pat)
      (rename-pattern-variables pat renaming qd))
    
    (define (recur-pats pats)
      (for/list ([pat pats])
        (recur pat)))

    (match pat
      ;; Quotes
      [`((ref |`|) ,pat0)
       `((ref |`|) ,(rename-pattern-variables pat0 renaming (+ qd 1)))]
      [`((ref |,|) ,pat0) #:when (= qd 0)
       pat]
      [`((ref |,|) ,pat0)
       `((ref |,|) ,(rename-pattern-variables pat0 renaming (- qd 1)))]
      
      ;; Constants
      [`(const ,v)
       pat]

      ;; ref pattern qd>0 
      [`(ref ,x) #:when (> qd 0)
       pat]

      ;; ref pattern qd=0
      [`(ref _) #:when (= qd 0) pat]
      [`(ref ,x) #:when (= qd 0)
       `(ref ,(hash-ref renaming x))]

      ;; = and &
      [`((ref =) (ref ,px) ,pats ...)
       `((ref =) (ref ,(hash-ref renaming px)) ,@(recur-pats pats))]
      [`((ref |&|) ,pats ...)
       `((ref |&|) ,@(recur-pats pats))]
      
      ;; Subwords
      [`((ref |[]|) ((ref |[]|) (ref ,tag) ,pat0))
       `((ref |[]|) ((ref |[]|) (ref ,tag) ,(recur pat0)))]

      ;; _slice
      [`((ref |[]|) (ref _slice) ,pat0)
       `((ref |[]|) (ref _slice) ,(recur pat0))]

      ;; Objects
      [`((ref |[]|) (ref ,tag) ,pats ...)
       #:when (and (> qd 0) (symbol? tag))

       `((ref |[]|) (ref ,tag) ,@(recur-pats pats))]
      
      ;; Slices
      [`((ref |[]|) ,pats ...)
       `((ref |[]|) ,@(recur-pats pats))]
      
      ;; ? patterns
      [`((ref |?|) (ref ,px) (ref ,pred))
       `((ref |?|) (ref ,(hash-ref renaming px)) (ref ,pred))]

      ;; ... patterns
      [`((ref ,ell) ,pat0) #:when (eq? ell '|...|)
       `((ref ,ell) ,(recur pat0))]
      
      [_
        (displayln (format "rename-pattern-variables failed for pattern: ~a" pat))
        (error 'rename-pattern-variables-error)]))

  ;; x is a ref expr evaluating to the match value (e.g. `(ref ,gx)`) which should be a slice
  ;; pats is a (ListOf Patterns)
  ;; body and fail-e must already be desugared
  ;; sig-params must not be desugared yet
  (define (desugar-pats x pats fail-e sig-params body [qd 0])
    (match pats
      ['()
        `(if (bless ((ref equal) (ref empty) ,x)) ,body ,fail-e)]
      
      ;; Simple ref with ...
      [(list `((ref ,ell) (ref ,pat))) #:when (eq? ell '|...|)
        (desugar-pat x `(ref ,pat) fail-e sig-params body qd)]
      
      ;; Complex pattern with ...
      [(list `((ref ,ell) ,pat)) #:when (eq? ell '|...|)
        (define pvs (set->list (gather-pattern-variables pat qd))) ; Pick an (arbitrary) order by converting to a list
        (define pv-refs (map (lambda (pv) `(ref ,pv)) pvs))

        (define renaming
          (for/hash ([pv pvs])
            (values pv (gensymb pv))))
        (define renamed-pat (rename-pattern-variables pat renaming))
        (define pvs^ (hash-values renaming))

        (define desguared-sig-params (map desugar-ast sig-params))

        ;; Initial accs: [] [] ...
        (define initial-accs
          (for/fold ([accs '()])
                    ([_ pvs])
            (cons '(|[]|) accs)))

        (define update-accs
          (for/list ([pv pvs]
                     [pv^ pvs^])
            `((ref +) (ref ,pv) (|[]| (ref ,pv^)))))
        
        (define desugared-update-accs (map desugar-ast update-accs))

        (define loop-x (gensymb 'loop))
        (define x-slice (gensymb 'x_slice))
        (define x-elm (gensymb 'x_elm))

        ;; TODO: remove duplicate is-splice? functions
        (define (is-splice? e)
         (match e
          [`((ref ,ell) ,_) #:when (eq? ell '|...|)
           #t]
          [_ #f]))
       
        ;; TODO: remove duplicate code in enter-loop-e and recur-loop-e
        (define enter-loop-e
          (cond
            ;; If a sig param is variadic, then splice it into the call to loop:
            [(ormap is-splice? sig-params)
              (define arg-list (desugar-ast `(|[]| ,x ,@initial-accs ,@sig-params)))
              `((ref _apply_with_fallback) (ref none) (ref ,loop-x) (ref ,fallback-x) ,arg-list)]

            ;; Normal loop call:
            [else
              `((ref ,loop-x) (ref ,fallback-x) ,x ,@initial-accs ,@desguared-sig-params)]))

        (define recur-loop-e
          (cond
            ;; If a sig param is variadic, then splice it into the call to loop:
            [(ormap is-splice? sig-params)
              (define arg-list (desugar-ast `(|[]| ((ref rest) (ref ,x-slice)) ,@update-accs ,@sig-params)))
              `((ref _apply_with_fallback) (ref none) (ref ,loop-x) (ref ,fallback-x) ,arg-list)]

            ;; Normal loop call:
            [else
              `((ref ,loop-x) (ref ,fallback-x) ((ref rest) (ref none) (ref ,x-slice)) ,@desugared-update-accs ,@desguared-sig-params)]))

        (define loop-def
          `(def ((ref ,loop-x) (ref ,fallback-x) (ref ,x-slice) ,@pv-refs ,@desguared-sig-params)
            (if ((ref is_empty) (ref none) (ref ,x-slice))
              ,body

              (let (ref ,x-elm) ((ref first) (ref none) (ref ,x-slice))
                ,(desugar-pat `(ref ,x-elm) renamed-pat fail-e sig-params
                    recur-loop-e
                    qd)))))

        (lift-def! loop-x loop-def)

        `(if ((ref is_slice) (ref none) ,x)
          ,enter-loop-e
          ,fail-e)]
      
      [(cons e0 es)
        (define gx0 (gensymb 'car))
        (define gx1 (gensymb 'cdr))
        `(let (ref
                ,gx0)
            ,(desugar-ast `((ref first) ,x))
            (if (bless ((ref equal) (ref none) (ref ,gx0)))
                ,fail-e
                ,(desugar-pat `(ref ,gx0)
                              e0
                              fail-e
                              sig-params
                              `(let (ref
                                    ,gx1)
                                ,(desugar-ast `((ref rest) ,x))
                                ,(desugar-pats `(ref ,gx1) es fail-e sig-params body qd))
                              qd)))]))

  ;; x is a ref expr evaluating to the match value (e.g. `(ref ,gx)`)
  ;; body and fail-e must already be desugared
  ;; sig-params must not be desugared yet
  (define (desugar-pat x pat fail-e sig-params body [qd 0])
    (define recur (lambda (pat0) (desugar-pat x pat0 fail-e sig-params body qd)))

    (match pat
      ;; Quote Patterns
      [`((ref |`|) ,e0)
       (desugar-pat x e0 fail-e sig-params body (+ qd 1))]
      [`((ref |,|) ,e0) #:when (= qd 0)
       `(if ((ref =) (ref none) ,x ,(desugar-ast e0))
            ,body
            ,fail-e)]
      [`((ref |,|) ,e0)
       (desugar-pat x e0 fail-e sig-params body (- qd 1))]

      [`(const ,v)
       `(if ((ref =) (ref none) ,x ,(desugar-ast `(const ,v)))
            ,body
            ,fail-e)]

      ;; ref pattern qd>0:  
      [`(ref ,y) #:when (> qd 0)
       `(if ((ref =) (ref none) ,x ,(desugar-ast `(const ,y)))
            ,body
            ,fail-e)]

      ;; ref pattern qd=0: lowers to a var ref (todo: enforce unification?)
      [`(ref _) #:when (= qd 0) body]
      [`(ref ,y) #:when (= qd 0)
       `(let (ref ,y) ,x ,body)]

      ;; Equal patterns 
      [`((ref =) (ref ,px) ,pats ...)
       (recur `((ref |&|) (ref ,px) ,@pats))]

      [`((ref |&|)) body]
      [`((ref |&|) ,pat0) (desugar-pat x pat0 fail-e sig-params body qd)]
      [`((ref |&|) ,pat0 ,pats ...)
       (desugar-pat x pat0 fail-e sig-params
                    (recur `((ref |&|) ,@pats))
                    qd)]

      ;; Special "_subword" patterns
      [`((ref |[]|) ((ref |[]|) (ref _subword) ,pat0))
       (define x+ (gensymb 'subword))
       `(if (bless ((ref equal) (ref _subword) ((ref get_subword_tag) ,x)))
            ,(desugar-pat x pat0 fail-e sig-params body qd)
            ,fail-e)]
      
      ;; Subword patterns for a single 56bit int
      [`((ref |[]|) ((ref |[]|) (ref ,tag) ,pat0))
       #:when (and (> qd 0) (symbol? tag))
       (define tag+ (private-subword-tag tag))
       (define tag-x (gensymb 'tag))
       (define sub-x (gensymb 'sub))
       `(if (bless ((ref equal) ((ref get_subword_tag) ,x) (ref ,tag+)))
            (let (ref ,sub-x) (bless ((ref box_subword)
                                        ((ref unbox_subword) ,x)
                                        (ref _subword)))
              ,(desugar-pat `(ref ,sub-x) pat0 fail-e sig-params body qd))
            ,fail-e)]

      ;; Special value patterns (slices, functions, etc)
      [`((ref |[]|) (ref _slice) ,e0)
       (define x+ (gensymb 'slice_ptr))
       `(if (bless ((ref equal) ((ref u64bit_and) (const 7) ,x) (const 2)))
            (let (ref ,x+) (bless ((ref top61) ,x))
              ,(desugar-pat `(ref ,x+) e0 fail-e sig-params body qd))
            ,fail-e)]
      
      ;; Object patterns
      [`((ref |[]|) (ref ,tag) ,es ...)
       #:when (and (> qd 0) (symbol? tag))
       (define tag+ (private-obj-tag tag))
       (define slice-x (gensymb 'obj_sl))
       ;; why does this break if I nest it directly, vs using ttt??
       `(let (ref ttt) (bless ((ref get_object_tag) ,x))
        (if (bless ((ref equal) (ref ttt) (ref ,tag+)))
            (let (ref ,slice-x) (bless ((ref get_object_slice) ,x))
              ,(desugar-pats `(ref ,slice-x) es fail-e sig-params body qd))
            ,fail-e))]

      ;; List patterns
      [`((ref |[]|) ,es ...)
        `(if ((ref is_slice) (ref none) ,x) ;; TODO: possibly allow [] patterns to match any iterable
             ,(desugar-pats x es fail-e sig-params body qd)
             ,fail-e)]

      ;; ? patterns
      [`((ref |?|) (ref ,pat) (ref ,pred))
       #:when (= qd 0)

       (define eval-pred
        `(if ((ref ,pred) (ref none) (ref ,pat))
             ,body
             ,fail-e))

       (desugar-pat x `(ref ,pat) fail-e sig-params eval-pred qd)]

      [`(,es ...) #:when (> qd 0) ;; TODO: is this case ever used?
       (desugar-pats x es fail-e sig-params body qd)]

      [_ 
        (displayln (format "desugar-pat failed for pattern: ~a" pat))
        (error 'desugar-pat)]))

  ;; Symbol Symbol AST -> AST
  ;; `name` is the function's new generated name and ast is the full def.
  ;; `failx` is the name of the next def to try if this current ones fails
  ;;    (i.e. if the params don't match).
  ;; `ast` is just the current def to desugar.
  (define (desugar-one-def name failx ast)
    (match ast
      [`(def ((ref ,fname) ,params ...) ,maybe-when ... ,body)

       ;; (ListOf PatternExpr) -> (ValuesOf (ListOf Symbol) Lambda)
       ;; Returns a list of pattern/param names and a binder lambda.
       ;; The binder lambda contains the built up output code to run the pattern matching.
       (define (process-params ps)
         (match ps
           ;; done with params
           ['()
            ;; pad check to ensure that the caller did not pass too many arguments
            (define pc (gensymb 'pad_check))

            (cond
              ;; Special case: don't add the pad check for _gather
              [(eq? fname '_gather)
                (values (list)
                        (lambda (b fail-ast sig-params)
                          b))]
              [else
                (values (list `(ref ,pc))
                        (lambda (b fail-ast sig-params)
                          `(if (bless ((ref equal) (ref _noarg) (ref ,pc))) ,b ,fail-ast)))])]
           
           ;; ellipsis case
           [(cons `((ref ,ell) ,inner-pat) rest-ps) #:when (eq? ell '|...|)
            (unless (null? rest-ps)
              (error 'desugar "Vararg splice (...) must be the final parameter in a definition."))
            (define rest-name (gensymb 'rest))
            (values (list `((ref ,ell) (ref ,rest-name))) ; Keep ... for use in later passes and for fail-e
                    (lambda (b fail-ast sig-params)
                      (desugar-pats `(ref ,rest-name) ps fail-ast sig-params b)))]
           
           ;; other cases
           [(cons pat rest-ps)
            ;; Generate param/pattern name
            (define px (match pat
                         [`(ref ,x) `(ref ,(if (eq? x '_) (gensymb '_) x))]
                         [`(const ,v) `(ref ,(gensymb 'const))]
                         [_ `(ref ,(gensymb 'pat))]))
            
            (let-values ([(rest-px binder) (process-params rest-ps)])
              (values (cons px rest-px)
                      (lambda (b fail-ast sig-params)
                        (define body (desugar-pat px pat fail-ast sig-params (binder b fail-ast sig-params)))
                        (if (eq? fname '_gather) ;; Special case: _gather allows passing _noarg
                            body
                            `(if (bless ((ref equal) (ref _noarg) ,px)) ,fail-ast ,body)))))]))
       
       ;; sig-params are the param names that will be matched on
       (define-values (sig-params body-binder) (process-params params))
       
       (define (is-splice? e)
         (match e
          [`((ref ,ell) ,_) #:when (eq? ell '|...|)
           #t]
          [_ #f]))
       
       ;; What to do if the patterns don't match: go to the next def (i.e. failx)
       (define fail-e
        (cond
          ;; If a sig param is variadic, then splice it into the call to failx:
          [(ormap is-splice? sig-params)
            (define arg-list (desugar-ast `(|[]| ,@sig-params)))
            `((ref _apply_with_fallback) (ref none) (ref ,failx) (ref ,fallback-x) ,arg-list)]

          ;; Normal failx call:
          [else
            `((ref ,failx) (ref ,fallback-x) ,@sig-params)]))

       ;; Call desugar-ast on each param in the case there is a (ref ...) that needs the ref removed
       (define desguared-sig-params (map desugar-ast sig-params))

       `(def ((ref ,name) (ref ,fallback-x) ,@desguared-sig-params)
          ,(body-binder 
            `(if ,(desugar-ast `((ref |&|) ,@maybe-when)) ; if the when exists: evaluate it otherwise the & is empty so just continue normally
                 ,(desugar-ast body) ; if the when suceedes (or there is no when guard)
                 ,fail-e)            ; else fail
            fail-e
            sig-params))]))
  
  ;; The main desugarer
  (define (desugar-ast ast [qd 0])
    ;; Desugar expression ASTs 
    (match ast
      ;; Ellipsis
      [`((ref ,ell) ,e0)
       #:when (eq? ell '|...|)
       `(,ell ,(desugar-ast e0 qd))]
      
      ;; Desugar quoted data
      [`((ref |`|) ,e0)
       (desugar-ast e0 (+ qd 1))]

      [`((ref |,|) ,e0)
       (desugar-ast e0 (- qd 1))]

      ;; Lift constants out (fixint sized integers)
      [`(const ,(? integer? z))
       #:when (< (- 0 (expt 2 48)) z (expt 2 48))
       ;; first none is for the fallback as this is an external call
       `((ref _init_from_s64) (ref none) (ref none) (bless (const ,z)))]
      [`(const ,(? integer? z))
       ;; first none is for the fallback as this is an external call
       `((ref _init_from_int_cstr) (ref none) (ref none) (bless (const ,(~s (~a z)))))]
      [`(const ,(? string? s))
       ;; second none here is idiom to avoid dispatch on naked values
       `((ref _init_from_cstr) (ref none) (ref none) (bless (const ,(~s s))))]
      
      ;; Quoted sub-word values
      [`((ref |[]|) ((ref |[]|) (ref ,tag) ,es ...))
       #:when (and (> qd 0) (symbol? tag))
       (define tag+ (private-subword-tag tag))
       `(subword (ref ,tag+)
                 ,@(map (lambda (e) (desugar-ast e qd)) es))]

      ;; Quoted objects
      [`((ref |[]|) (ref ,tag) ,es ...)
       #:when (and (> qd 0) (symbol? tag))
       (define tag+ (private-obj-tag tag))
       `(object (ref ,tag+)
          ,@(map (lambda (e) (desugar-ast e qd)) es))]

      ;; Quoted list builder
      [`(,es ...) #:when (> qd 0)
       (desugar-ast `(|[]| ,@es) qd)]

      ;; Quoted symbols
      [`(ref ,x) #:when (> qd 0)
       (desugar-ast x)]

      ;; Leave some forms alone
      [(or 'ref 'top-level) ast]
      [`(ref ,x) ast]
      [(? symbol? x) `(ref ,x)] ;; Just in case a bare symbol leaks through

      ;; Desugar and/or
      [`((ref |&|)) '(ref true)]
      [`((ref |&|) ,e0) (desugar-ast e0)]
      [`((ref |&|) ,e0 ,es ...)
       (desugar-ast
        `(if ,e0
             ((ref |&|) ,@es)
             (ref false)))]
      
      [`(,or) ;; otherwise racket doesn't love using pipe as a sym
       #:when (equal? or `(ref ,(string->symbol "|")))
       '(ref false)]
      [`(,or ,e0)
       #:when (equal? or `(ref ,(string->symbol "|")))
       (desugar-ast e0)]
      [`(,or ,e0 ,es ...)
       #:when (equal? or `(ref ,(string->symbol "|")))
       (define gx (gensymb 'or))
       (desugar-ast
        `(let (ref ,gx) ,e0
              (if (ref ,gx)
                  (ref ,gx)
                  ((ref ,(string->symbol "|")) ,@es))))]

      ;; Handle simple let patterns by recuring
      [`(let (ref ,x) ,rhs ,body)
       `(let (ref ,x) ,(desugar-ast rhs) ,(desugar-ast body))]
      
      ;; Handle general let patterns with desugar-pat helper
      [`(let ,pat ,rhs ,body)
       (define fail-e
         (desugar-ast `(bless ((ref fatal) (const "\"Let pattern failure.\"")))))
       (define rhsx (gensymb 'rhs))
       `(let (ref ,rhsx) ,(desugar-ast rhs)
	     ,(desugar-pat `(ref ,rhsx) pat fail-e '() (desugar-ast body)))]
      
      [`(if ,g ,t ,e)
       `(if ,(desugar-ast g) ,(desugar-ast t) ,(desugar-ast e))]

      [`((ref |[]|) ,es ...)
       (desugar-ast `(|[]| ,@es) qd)] ; Remove ref
      [`(|[]|) `(ref empty)]
      [`(|[]| ,es ...)
       (define chunks
        (filter (lambda (e) (match e [`((ref |[]|)) #f] [_ #t]))
          (foldl
            (lambda (e0 acc)
              (match `(,e0 ,acc)
                [`(((ref ,ell) ,e1) (,old ... ,this))
                  #:when (eq? ell '|...|)
                  `(,@old ,this ,(desugar-ast e1) (|[]|))] ;; Put e1 into it's own chunk
                [`(,e1 (,old ... ,this))
                  `(,@old (,@this ,(desugar-ast e1)))])) ;; Keep in the same `this` chunk
            '((|[]|))
            es)))
      
       ;; Concatenate (i.e. splice) the chunks together
       (match chunks
        [`() `(ref empty)] 
        [`(,e0 ,es ...)
          (foldl (lambda (e1 e0) `((ref +) (ref none) ,e0 ,e1)) e0 es)])]

      [`((ref |{}|)) '(ref none)]
      [`((ref |{}|) ,es ... ,elast)
       (desugar-ast
        (foldr (lambda (e bdy)
                 `(let (ref ,(gensymb '_))
                    ,e ,bdy))
               elast
               es))]
      
      ;; Bless expression
      [`(bless ,es ...) `(bless ,@es)]

      ;; Untagged application
      [`(,ef ,es ...)
       (define ef+ (desugar-ast ef qd))
       (define es+ (map (lambda (e) (desugar-ast e qd)) es))
       (define (is-splice? e)
         (match e [`(|...| ,_) #t] [_ #f]))
       (cond
        [(or (equal? ef+ '(ref raw_apply)) (equal? ef+ '(ref raw_apply_with_fallback))) ; Special cases that don't require a fallback arg
          `(,ef+ ,@es+)]
        [(ormap is-splice? es+)
          (define arg-list (desugar-ast `(|[]| ,@es) qd))
          `((ref _apply) (ref none) ,ef+ ,arg-list)]
        [else
          `(,ef+ (ref none) ,@es+)])]
      
      ;; Otherwise error
      [_ (pretty-print ast) (error 'desugar-ast-err)]))
  
  ;; returns an obj tag if its an obj pat, or #f if not
  (define (object-method-pat? pat [qd 0])
    (define (recur? pat) (object-method-pat? pat qd))
    (match pat
      [`((ref |`|) ,e0)
       (object-method-pat? e0 (+ qd 1))]
      [`((ref |,|) ,e0)
       (object-method-pat? e0 (- qd 1))]
      
      [`((ref =) ,es ...) (ormap recur? es)]
      [`((ref |&|) ,es ...) (ormap recur? es)]
      [`((ref ,ell) ,e0)
       #:when (eq? ell '|...|)
       (recur? e0)]

      ;; Return the tag symbol as truthy affirm when qd>0 at [tag ...]
      [`((ref |[]|) ((ref |[]|) (ref ,tag) ,_ ...))
       #:when (and (> qd 0) (symbol? tag))
       (cons 'subword tag)]
      [`((ref |[]|) (ref ,tag) ,_ ...)
       #:when (and (> qd 0) (symbol? tag))
       (cons 'object tag)]

      [_ #f]))
  
  ;; filters top-level ast of defs into a map obj -> ast
  (define (part-by-objects lst)
    (match lst
      [`() (hash)]
      [`((def ((ref ,name) ,args ...)
	      ,maybe-when ... ,body) ,more ...)
       (define obj (if (null? args) #f (object-method-pat? (car args))))
       (define tails (part-by-objects more))
       (hash-set tails obj
        (cons `(def ((ref ,name) ,@args)
                 ,@maybe-when ,body)
		          (hash-ref tails obj list)))]))
  
  ;; Desugar an ordered list of defs
  (define (desugar-defs lst)
    (define parts (part-by-objects lst))

    (foldr ; flatten by one level
     append '()
     (for/list ([(obj-info ls) (in-hash parts)])
      (let loop ([ls ls]
		             [next-x #f])
        (match ls
          ['()
            ;; params to pass on to the fallback (so-far is 2 since we generate the fallback and overflow-splice args seperately)
            (define params (pad-params 2))

            (define params-rest-x (gensymb 'rest-params))
            (define ell '|...|)

            ;; (... params-rest-x) will bind to a slice which is directly passed via continue-dispatch
            `((def ((ref ,next-x) (ref ,fallback-x) ,@params (,ell (ref ,params-rest-x)))
              (continue-dispatch (ref ,fallback-x) ,@params (ref ,params-rest-x))))] ;; continue-dispatch: a special form (removed later on) that continues with the fallback
          [`((def ((ref ,x) ,_ ...) ,_ ...) ,more ...)
            #:when obj-info ;; This is an obj-pattern def:
            (match-define (cons kind obj-tag) obj-info)
            (define mynext (gensymb x))
            (define tag+ (if (eq? kind 'subword)
                             (private-subword-tag obj-tag)
                             (private-obj-tag obj-tag))) ;; else: (eq? kind 'object)
            (define gx
              (if next-x
                  next-x
                  (let* ([gx (method-publish-name x tag+)])
                    (register-method! x tag+ gx)
                    gx)))
            (cons (desugar-one-def gx mynext (first ls))
                  (loop more mynext))]
          ;; For all non-obj-pattern defs:
          [`((def ((ref ,x) ,_ ...) ,_ ...) ,more ...)
            (define mynext (gensymb x))
            (define gx
              (if next-x
                  next-x
                  (let ([gx (gensymb x)])
                    ;; register just this first one
                    (register-method! x #f gx)
                    gx)))
            (cons (desugar-one-def gx mynext (first ls))
                  (loop more mynext))])))))

  ;; Body of desugar-module
  (match mod
    [`(module ,name ,bless ,all-inline
	      ,blessed ,lets ,defs)

     (define defs+
      (foldl (lambda (name defs+) ;; 2. add new/lifted defs
              (cons (hash-ref lifted-defs name) defs+))
             (foldl (lambda (kv defs+) ;; 1. desugar defs
                      (append (desugar-defs (cdr kv)) defs+))
                    '()
                    defs)
             (hash-keys lifted-defs)))

     (define init-def
       `(def ((ref ,(sym-append "entry_point_" this-mod-tag)) (ref _fb))
	     ,(desugar-ast
	       `((ref |{}|)
            ,@(map (lambda (letast)
                    (match letast 
                      [`(let (ref ,x) ,rhs)
                        (define x+ (gensymb x))
                        `(let (ref ,x+) ,rhs
                        (bless ((ref assign)
                          ;; hides from renaming?
                          (const ,(format "~a"
                              (escape-id-for-C x)))
                          (ref ,x+))))]
                      [_ (pretty-print letast)
                          (error "Todo: add top-level let patterns")]))
                  lets)))))

     `(module ,name ,this-mod-tag ,bless ,all-inline
	      ,blessed ,lets ,(cons init-def defs+)
	      ,(hash->list method-map)
	      ,(set->list types-st))]))


