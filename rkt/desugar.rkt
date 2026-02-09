#lang racket

(require "utils.rkt"
	 "langs.rkt")

(provide desugar-module)

(define old-const (make-hash))


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
        ['() `(if (bless ((ref equal) (ref empty) ,x))
                  ,body ,fail-e)]
        [(cons e0 es)
         (define gx0 (gensymb 'car))
         (define gx1 (gensymb 'cdr))
         `(let (ref ,gx0)
            ,(desugar-ast
              `((ref first) ,x))
            (if (bless ((ref equal) (ref none) (ref ,gx0)))
		,fail-e 
		,(desugar-pat `(ref ,gx0) e0 fail-e
                              `(let (ref ,gx1)
				 ,(desugar-ast
                                   `((ref rest) ,x))
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
      [`((ref |[]|) ,es ...) #:when (= qd 0)
       (slice-pat x es)]

      [`(,es ...) #:when (> qd 0)
       (slice-pat x es)]

      [_ (error 'desugar-pat)]))

  (define (desugar-one-def name failx ast)
    (match ast
      [`(def ((ref ,_) ,params ...) ,maybe-when ... ,body)
       (define oneslice
	 (lambda ()
	   (set! oneslice (lambda () #t))
	   #f))
       (define (pat->param pat)
	 (match pat
	   [`(ref ,x) `(ref ,(if (eq? x '_) (gensymb '_) x))]
	   [`(const ,v) `(ref ,(gensymb 'const))]	       
	   [`((ref ,ell) (ref ,x))
	    #:when (equal? ell '|...|)
	    (when (oneslice) (error 'ambiguous-slices))
	    `((ref ,ell) (ref ,(if (eq? x '_) (gensymb '_) x)))]
	   [_ `(ref ,(gensymb 'pat))]))
       (define params-x (map pat->param params))
       (when (and (oneslice)
		  (list? (car (last params-x)))
		  (eq? '|...| (second (car (last params-x)))))
	 (error 'non-tail-slice))
       (define fail-e `((ref ,failx) (ref ,fallback-x) ,@params-x))
       
       `(def ((ref ,name) (ref ,fallback-x) ,@params-x)
	     ,(foldr (lambda (x pat body)
		       (desugar-pat x pat fail-e body))
		     `(if ,(desugar-ast `((ref |&|) ,@maybe-when))
			  ,(desugar-ast body)
			  ,fail-e)
		     params-x
		     params))]))
  
  (define (desugar-ast ast [qd 0])
    ;; Desugar expression ASTs 
    (match ast
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
              (if (ref ,gx) (ref ,gx)
		  ((ref ,(string->symbol "|")) ,@es))))]

      ;; Handle simple let patterns by recuring
      [`(let (ref ,x) ,rhs ,body)
       `(let (ref ,x) ,(desugar-ast rhs) ,(desugar-ast body))]
      
      ;; Handle general let patterns with desugar-pat helper
      [`(let ,pat ,rhs ,body)
       (define fail-e `((ref error0)))
       (define rhsx (gensymb 'rhs))
       `(let (ref ,rhsx) ,(desugar-ast rhs)
	     (desugar-pat `(ref ,rhsx) pat fail-e (desugar-ast body)))]
      
      [`(if ,g ,t ,e)
       `(if ,(desugar-ast g) ,(desugar-ast t) ,(desugar-ast e))]

      [`((ref |[]|) ,es ...)
       (desugar-ast `(|[]| ,@es))]
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
       `(,(desugar-ast ef) (ref none) ,@(map desugar-ast es))]

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
    (foldr
     append '()
     (for/list
      ([(obj-info ls) (in-hash parts)])
      (let loop ([ls ls]
		 [next-x #f])
	(match ls
	  ['()
	   (define params (pad-params 1))
	   `((def ((ref ,next-x) (ref ,fallback-x) ,@params)
		  (continue-dispatch (ref ,fallback-x) ,@params)))]
	  [`((def ((ref ,x) ,_ ...) ,_ ...) ,more ...)
	   #:when obj-info ;; This is an obj-pattern def:
	   (match-define (cons kind obj-tag) obj-info)
	   (define mynext (gensymb x))
	   (define tag+ (if (eq? kind 'subword)
			    (private-subword-tag obj-tag)
			    (private-obj-tag obj-tag)))
	   (define gx (if next-x next-x
			  (let* ([gx (method-publish-name x tag+)])
			    (register-method! x tag+ gx)
			    gx)))
	   (cons (desugar-one-def gx mynext (first ls))
		 (loop more mynext))]
	  ;; For all non-obj-pattern defs:
	  [`((def ((ref ,x) ,_ ...) ,_ ...) ,more ...)
      	   (define mynext (gensymb x))
	   (define gx (if next-x next-x
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
       (foldl (lambda (name defs+) ;; 2. Add new/lifted defs
		(cons (cons name (hash-ref lifted-defs name))
		      defs+))
              (foldl (lambda (kv defs+) ;; 1. Desugar defs
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


