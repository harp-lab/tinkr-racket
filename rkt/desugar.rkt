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

  (define special '(_slice _fun_ptr _subword))
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

  ;; desugar-pat
  ;; x is a ref expr evaluating to the match value (e.g. `(ref ,gx)`)
  ;; body and fail-e must already be desugared
  (define (desugar-pat x pat fail-e body [qd 0])

    (define recur (lambda (pat0) (desugar-pat x pat0 fail-e body qd)))

    (define (slice-pat x elst)
      (match elst
        ['()
          `(if (bless ((ref equal) (ref empty) ,x)) ,body ,fail-e)]
        [(list `((ref ,ell) ,pat)) #:when (eq? ell '|...|)
          (desugar-pat x pat fail-e body qd)]
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
                                `(let (ref
                                      ,gx1)
                                  ,(desugar-ast `((ref rest) ,x))
                                  ,(slice-pat `(ref ,gx1) es))
                                qd)))]))

    (match pat
      ;; Quote Patterns
      [`((ref |`|) ,e0)
       (desugar-pat x e0 fail-e body (+ qd 1))]
      [`((ref |,|) ,e0) #:when (= qd 0)
       `(if ((ref =) (ref none) ,x ,(desugar-ast e0))
            ,body
            ,fail-e)]
      [`((ref |,|) ,e0)
       (desugar-pat x e0 fail-e body (- qd 1))]

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
      [`((ref |&|) ,pat0) (desugar-pat x pat0 fail-e body qd)]
      [`((ref |&|) ,pat0 ,pats ...)
       (desugar-pat x pat0 fail-e
                    (recur `((ref |&|) ,@pats))
                    qd)]

      ;; Special "_subword" patterns
      [`((ref |[]|) ((ref |[]|) (ref _subword) ,pat0))
       (define x+ (gensymb 'subword))
       `(if (bless ((ref equal) (ref _subword) ((ref get_subword_tag) ,x)))
	    ,(desugar-pat x pat0 fail-e body qd)
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
		 ,(desugar-pat `(ref ,sub-x) pat0 fail-e body qd))
	    ,fail-e)]

      ;; Special value patterns (slices, functions, etc)
      [`((ref |[]|) (ref _slice) ,e0)
       (define x+ (gensymb 'slice_ptr))
       `(if (bless ((ref equal) ((ref u64bit_and) (const 7) ,x) (const 2)))
	    (let (ref ,x+) (bless ((ref top61) ,x))
		 ,(desugar-pat `(ref ,x+) e0 fail-e body qd))
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
		      ,(slice-pat `(ref ,slice-x) es))
		 ,fail-e))]

      ;; List patterns
      [`((ref |[]|) ,es ...)
       (slice-pat x es)]

      [`(,es ...) #:when (> qd 0)
       (slice-pat x es)]

      [_ (error 'desugar-pat)]))

  ;; Symbol Symbol AST -> AST
  ;; `name` is the function's new generated name and ast is the full def.
  ;; `failx` is the name of the next def to try if this current ones fails
  ;;    (i.e. if the params don't match).
  ;; `ast` is just the current def to desugar.
  (define (desugar-one-def name failx ast)
    (match ast
      [`(def ((ref ,fname) ,params ...) ,maybe-when ... ,body)

       ;; (ListOf param) Int (or #f OverflowIndicator) -> (ValuesOf (ListOf Symbol) Lambda)
       ;; `overflow-x` is a name reference bound to the rest of the overflow list.
       ;; Returns a list of pattern/param names and a binder lambda.
       ;; The binder lambda contains the built up output code to bind and unpack the overflow list.
       (define (process-params ps idx overflow-x)
         (match ps
           ['() ; done with params: add checks that there are no left over arguments
            (cond
              [(< idx 6)
               (let ([pc (gensymb 'pad_check)])
                 (values (list `(ref ,pc))
                         (lambda (b fail-ast) ;; check that the next param doesn't exist
                           `(if (bless ((ref equal) (ref _noarg) (ref ,pc))) ,b ,fail-ast))))]
              [(= idx 6)
               (let ([pc (gensymb 'pad_check)])
                 (values (list `(ref ,pc))
                         (lambda (b fail-ast) ;; check that the current param is empty or doesn't exist
                           `(if (bless ((ref equal) (ref _noarg) (ref ,pc)))
                                ,b
                                (if (bless ((ref equal) (ref empty) (ref ,pc))) ,b ,fail-ast)))))]
              [else
               (values '()
                       (lambda (b fail-ast) ;; check that the rest of the overflow is empty
                         (if overflow-x
                             `(if (bless ((ref equal) (ref empty) ,overflow-x)) ,b ,fail-ast)
                             b)))])]
           
           ;; ellipsis case
           [(cons `((ref ,ell) ,inner-pat) rest-ps) #:when (eq? ell '|...|)
            (unless (null? rest-ps)
              (error 'desugar "Vararg splice (...) must be the final parameter in a definition."))
            (define rest-name (gensymb 'rest))
            (if (< idx 6)
                (let* ([remaining (- 6 idx)]
                       [gather-vars (for/list ([i (in-range remaining)]) (gensymb 'gather))]
                       [gather-refs (map (lambda (v) `(ref ,v)) gather-vars)]
                       [slice-var (gensymb 'gather_slice)]
                       [pad-noargs (for/list ([i (in-range (- 6 remaining))]) '(ref _noarg))])
                  (values `(,@gather-refs (ref ,slice-var))
                          (lambda (b fail-ast)
                            `(let (ref ,rest-name) 
                               ((ref _gather) (ref none) ,@gather-refs ,@pad-noargs (ref ,slice-var))
                               ,(desugar-pat `(ref ,rest-name) inner-pat fail-ast b)))))
                (values '()
                        (lambda (b fail-ast)
                          (desugar-pat overflow-x inner-pat fail-ast b))))]
           
           ;; other cases
           [(cons pat rest-ps)
            ;; Generate param/pattern name
            (define px (match pat
                         [`(ref ,x) `(ref ,(if (eq? x '_) (gensymb '_) x))]
                         [`(const ,v) `(ref ,(gensymb 'const))]
                         [_ `(ref ,(gensymb 'pat))]))
            
            ;; 3 Cases:
            (if (or (< idx 6) ;; 1. Fits in the first 5 tinkr arguments
                    (eq? fname '_gather)) ; _gather is a special exception where the last argument
                                          ; (the 6th tinkr one or 7th blessed one) passes the rest
                                          ; of the arguments as a slice instead of individually.
                (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) #f)])
                  (values (cons px rest-px)
                          (lambda (b fail-ast)
                            (define match-logic (desugar-pat px pat fail-ast (binder b fail-ast)))
                            (if (eq? fname '_gather)
                                match-logic
                                `(if (bless ((ref equal) (ref _noarg) ,px)) ,fail-ast ,match-logic)))))
                (if (= idx 6)
                    ;; 2. The first argument to put into the overflow list
                    (let* ([slice-x (gensymb 'overflow)]
                           [slice-ref `(ref ,slice-x)]
                           [next-slice-x (gensymb 'overflow_rest)])
                      (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) `(ref ,next-slice-x))])
                        (values (cons slice-ref rest-px)
                                (lambda (b fail-ast) ;; Builds up output code to unpack the overflow list
                                  `(if (bless ((ref equal) (ref _noarg) ,slice-ref)) ;; Check overflow arg exists
                                       ,fail-ast
                                       (if (bless ((ref equal) (ref empty) ,slice-ref)) ;; Check not empty
                                           ,fail-ast
                                           (let ,px ((ref first) (ref none) ,slice-ref) ;; Bind the arg to the pattern name
                                             (let (ref ,next-slice-x) ((ref rest) (ref none) ,slice-ref) ;; Continue with the rest of the overflow list
                                               ,(desugar-pat px pat fail-ast (binder b fail-ast))))))))))
                    ;; 3. Put the rest of the arguments in the over flow list
                    (let* ([next-slice-x (gensymb 'overflow_rest)])
                      (let-values ([(rest-px binder) (process-params rest-ps (+ idx 1) `(ref ,next-slice-x))])
                        (values rest-px 
                                (lambda (b fail-ast)
                                  `(if (bless ((ref equal) (ref empty) ,overflow-x)) ;; Check not empty
                                       ,fail-ast
                                       (let ,px ((ref first) (ref none) ,overflow-x) ;; Bind
                                         (let (ref ,next-slice-x) ((ref rest) (ref none) ,overflow-x) ;; Continue with the rest
                                           ,(desugar-pat px pat fail-ast (binder b fail-ast)))))))))))]))
       
       (define-values (params-x body-binder) (process-params params 0 #f))

       ;; These are the non-overflow params + the one overflow param list to put into the def signature
       (define sig-params
         (let loop ([pxs params-x] [sofar 1])
           (if (>= sofar bless-arg-count)
               '() ;; TODO: is this correct correct?
               (if (null? pxs)
                   (cons `(ref ,(gensymb '_)) (loop '() (add1 sofar)))
                   (cons (car pxs) (loop (cdr pxs) (add1 sofar)))))))
       
       ;; What to do if the patterns don't match: go to the next def (i.e. failx)
       (define fail-e `((ref ,failx) (ref ,fallback-x) ,@sig-params))

       `(def ((ref ,name) (ref ,fallback-x) ,@sig-params)
          ,(body-binder 
            `(if ,(desugar-ast `((ref |&|) ,@maybe-when)) ; if the when exists: evaluate it otherwise the & is empty so just continue normally
                 ,(desugar-ast body) ; if the when suceedes (or there is no when guard)
                 ,fail-e)            ; else fail
            fail-e))]))
  
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
	     ,(desugar-pat `(ref ,rhsx) pat fail-e (desugar-ast body)))]
      
      [`(if ,g ,t ,e)
       `(if ,(desugar-ast g) ,(desugar-ast t) ,(desugar-ast e))]

      [`((ref |[]|) ,es ...)
       (desugar-ast `(|[]| ,@es) qd)]
      [`(|[]|) `(ref empty)]
      [`(|[]| ,es ...)
       (define chunks
        (filter (lambda (e) (match e [`((ref |[]|)) #f] [_ #t]))
          (foldl (lambda (e0 acc)
              (match `(,e0 ,acc)
                [`(((ref ,ell) ,e1) (,old ... ,this))
                #:when (eq? ell '|...|)
                `(,@old ,this ,(desugar-ast e1) (|[]|))]
                [`(,e1 (,old ... ,this))
                `(,@old (,@this ,(desugar-ast e1)))]))
            '((|[]|))
            es)))
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
        [(equal? ef+ '(ref raw_apply))
              `(,ef+ ,@es+)]
              [(ormap is-splice? es+)
                (define arg-list (desugar-ast `(|[]| ,@es) qd))
                `((ref _apply) (ref none) ,ef+ ,arg-list)]
              [(< (length es+) (- bless-arg-count 2))
                ;; Fits perfectly in a0-a5: prepend the fallback
                `(,ef+ (ref none) ,@es+)]
        [else ;; Overflow: gather tail into a slice
              (define head (take es+ (- bless-arg-count 2)))
              (define raw-tail (drop es (- bless-arg-count 2)))
              (define residual-slice (desugar-ast `(|[]| ,@raw-tail) qd))
              `(,ef+ (ref none) ,@head ,residual-slice)])]
      
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
            (define params (pad-params 1))
            `((def ((ref ,next-x) (ref ,fallback-x) ,@params)
              (continue-dispatch (ref ,fallback-x) ,@params)))] ;; continue-dispatch: a special form (removed later on) that continues with the fallback
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
              (cons (cons name (hash-ref lifted-defs name)) defs+))
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


