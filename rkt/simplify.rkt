#lang racket

(require "utils.rkt")
(require "langs.rkt")

(provide (contract-out
          [alphatize (-> sm-core-ir? sm-core-ir?)]
	  [anf-convert (-> sm-core-ir? sm-core-ir?)]
	  [simplify-module (-> any/c any/c)]))


(define global-names 0) ;; (set)
(define reserved-bl-x (set '|!|))

(define (alphatize ast) 

  ;; Alphatize let or def body
  (define (alphatize+ ast [env (hash)])
    (define (recur ast) (alphatize+ ast env))
    (define (resolve-id x)
       (define x+ (escape-id-for-C (hash-ref env x (lambda () x))))
       (if (eq? x+ '_u_0003d) 'v_equal x+))
    
    (define (T-bl ast)
      (match ast
        ;; Refs that are not reserved-bl-x
        [`(const ,_) ast]
        [`(ref ,x) #:when (set-member? reserved-bl-x x) ast]
        [`(ref ,x)
        (define x+ (resolve-id x))
        (when (not (hash-has-key? env x))
          (set! global-names (set-add global-names x+)))
        `(ref ,x+)]
        ;; Untagged application
        [`(,fx ,es ...) `(,fx ,@(map T-bl es))]
        ;; Otherwise leave it alone
        [_ ast]))
    
    (match ast
      ;; Update reference
      [`(ref ,x)
       (define x+ (resolve-id x))
       (when (not (hash-has-key? env x))
        (set! global-names (set-add global-names x+)))
       `(ref ,x+)]

      ;; No change to constants, blessed
      [`(const ,_) ast]
      [`(bless ,e0) `(bless ,(T-bl e0))]

      ;; Simple recursion
      [`(if ,g ,t ,e) `(if ,(recur g) ,(recur t) ,(recur e))]

      [`(continue-dispatch ,es ...)
       `(continue-dispatch ,@(map recur es))]

      [`(,ell ,e0) #:when (eq? ell '|...|)
       `(,ell ,(recur e0))]
      
      [`(,(and ctor (or 'object 'subword)) ,es ...)
       `(,ctor ,@(map recur es))]

      ;; Remove pointless lets
      [`(let (ref ,x) (ref ,y) ,body)
       (alphatize+ body (hash-set env x (hash-ref env y (lambda () y))))]

      ;; Let
      [`(let (ref ,x) ,rhs ,body)
       (define x+ (gensymb x))
       `(let (ref ,(escape-id-for-C x+)) ,(recur rhs)
             ,(alphatize+ body (hash-set env x x+)))]

      ;; slices
      [`(|[]| ,es ...)
       `(|[]| ,@(map recur es))]

      ;; Untagged application
      [`((ref ,fx) ,es ...) (map recur ast)]

      [_ (pretty-print ast)
        (error 'alphatize-error)]))
  
  (match ast
    [`(let ,lhs ,rhs)
     `(let ,(alphatize+ lhs) ,(alphatize+ rhs))]

    ;; Alphatize defs (w/ param alpha-renaming)
    [`(def ((ref ,fx) ,args ...) ,body)
     (define env (hash))
     (define args+
       (for/list ([arg (in-list args)])
         (match arg
           [`(ref ,x)
            (define x+ (gensymb x))
            (set! env (hash-set env x x+))
            `(ref ,(escape-id-for-C x+))]
           [`(,ell (ref ,x)) #:when (eq? ell '|...|)
            (define x+ (gensymb x))
            (set! env (hash-set env x x+))
            `(,ell (ref ,(escape-id-for-C x+)))])))
     `(def ((ref ,(escape-id-for-C fx)) ,@args+)
        ,(alphatize+ body env))]

    [_ (pretty-print ast)
       (error 'alphatize)]))


;; Normalizes sub-expressions so they are let bound
;; Normalizes some simple forms into blessed code and junctures with blessed code
(define (anf-convert ast)
  
  (define (normalize-term ast)
    (normalize ast (λ (x) x)))

  (define (normalize ast k)
    (match ast
      [`(ref ,x) (k `(ref ,x))]
      
      [`(const ,v) (k `(const ,v))]

      [`(,ell ,e) #:when (eq? ell '|...|) (k `(,ell ,e))]
      
      [`(bless ,e0)
       (define gx (gensymb 'bl))
       `(let (ref ,gx) ,ast ,(k `(ref ,gx)))]

      [`(,(and ctor (or 'object 'subword '|[]|)) ,eas ...)
       (normalize-names eas
                        (λ (xs)
			  (define t (gensymb 'rv))
                          `(let (ref ,t) (,ctor ,@xs)
				,(k `(ref ,t)))))]


      [`(let ,x ,e0 ,e1)
       (match e0 ;; When the cont is small enough, duplicate it freely
	 [`(if ,g ,t ,e) #:when (small-expr? e1)
	  (normalize `(if ,g (let ,x ,t ,e1) (let ,x ,e, e1)) k)]
	 [_ (normalize e0
		       (λ (e0+)
			 `(let ,x ,e0+
			       ,(normalize e1 k))))])]

      [`(if ,e0 ,e1 ,e2)
       (normalize-name e0
                       (λ (x)
                         (k `(if ,x
                                 ,(normalize-term e1)
                                 ,(normalize-term e2)))))]

      [`(continue-dispatch ,eas ...)
       (normalize-names eas
                        (λ (xs)
                          (k `(continue-dispatch ,@xs))))]

      [`(,eas ...)
       (normalize-names eas
                        (λ (xs)
                          (k `(,@xs))))]

      [_ (error 'normalize-err)]))

  (define (normalize-name e0 k)
    (match e0
      [`(,_ ...)
       (normalize e0
                  (λ (e0+)
                    (match e0+
                      [`(ref ,_) (k e0+)]
                      [`(const ,_) (k e0+)]
		      [`(,ell (ref ,_)) #:when (eq? ell '|...|) (k e0+)]
                      [_ (let ([tx `(ref ,(gensymb 't))])
                           `(let ,tx ,e0+ ,(k tx)))])))]))

  (define (normalize-names es k)
    (if (null? es)
        (k '())
        (normalize-name (car es)
                        (λ (tx)
                          (normalize-names (cdr es)
                                           (λ (txs)
                                             (k `(,tx ,@txs))))))))

  (match ast
    [`(def ,param ,body)
     `(def ,param ,(normalize-term body))]
    
    [`(let ,name ,rhs)
     `(let ,name ,(normalize-term rhs))]

    [_ (error 'anf-convert-err)]))


(define (cps-convert ast)
  ;; Blessed compilation below adds stack push/pop
  ;;   this code compiles to use these to push
  ;;   a closure for each cont: freevars + fptr

  (define lifted-defs '())
  (define (lift-def! def) (set! lifted-defs (cons def lifted-defs)))
  
  (define (all-local-work? ast)
    (match ast ;; does this ast compile without nonlocal jumps?
      [`(,(or 'bless 'const 'ref 'object 'subword) ,_ ...) #t]
      [`((ref ,fx) ,_ ...) (set-member? reserved-bl-x fx)]
      [`(if ,es ...) (andmap all-local-work? es)]
      [`(let ,_ ,e0 ,e1)
       (and (all-local-work? e0) (all-local-work? e1))]
      [_ #f]))
  
  (define (T-cps ast defname)
    (define (recur ast) (T-cps ast defname))

    (define (free ast)
      (define (freevars ast)
	(define (freebless ast)
	  (match ast
	    [`(ref ,x) (set x)]
	    [`(,fe ,aes ...) ;; do not count fun-expr
	     (foldl set-union (set) (map freevars aes))]
	    [_ (set)]))
	(match ast
	  [`(ref ,x) (set x)]
	  [`(bless ,e0) (freebless e0)]
	  [`(let ,lhs ,rhs ,body)
	   (set-union (freevars rhs)
		      (set-subtract (freevars body) (freevars lhs)))]
	  [`(,es ...)
	   (foldl set-union (set) (map freevars es))]
	  [_ (set)]))
      (set-subtract (freevars ast) global-names reserved-bl-x
		    (set 'unbox_subword 'get_subword_tag)))

    (define (lift-cont! x body type rhs)
      
      (define freelst (set->list (set-remove (free body) x)))
      (define kname (gensymb (sym-append defname type)))
      (lift-def! ;; assumes def interface w/ dummy fallback
       `(def ((ref ,kname) (ref ,(gensymb '_)) (ref ,x))
	     ,(foldl (lambda (free-x body+)
		       `(let (ref ,free-x) (bless ((ref stack_pop)))
			     ,body+))
		     (recur body)
		     freelst)))
      (foldr (lambda (free-x body+)
	       `(let (ref ,(gensymb '_))
		  (bless ((ref stack_push) (ref ,free-x)))
                  ,body+))
             `(let (ref ,(gensymb '_))
		(bless ((ref stack_push) ((ref blessed_t) (ref ,kname))))
		,rhs)
             freelst))
    
    (match ast
      [(or `(ref ,_) `(const ,_)) `(return ,ast)]
      
      [`(let (ref ,x) ,(and atom (or `(ref ,_) `(const ,_))) ,body)
       `(let (ref ,x) ,atom
	     ,(recur body))]

      [`(let (ref ,x) (bless ,rhs) ,body)
       `(let (ref ,x) (bless ,rhs)
	     ,(recur body))]

      [`(let (ref ,x) (,(and ctor (or 'object 'subword '|[]|)) ,xs ...) ,body)
       `(let (ref ,x) (,ctor ,@xs)
	     ,(recur body))]
      
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       #:when (all-local-work? `(if ,g ,t ,e))
       `(let (ref ,x) (if ,g ,(recur t) ,(recur e)) ,(recur body))]
      
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       (lift-cont! x body "ifkont" `(if ,g ,(recur t) ,(recur e)))]
      
      [`(let (ref ,x) (,fx ,args ...) ,body)
       (lift-cont! x body "appkont" `(,fx ,@args))]

      [`(if ,guard ,then ,else) 
       `(if ,guard ,(recur then) ,(recur else))]
      [`(continue-dispatch ,_ ...) ast] 

      [`((ref ,fx) ,args ...)
       `((ref ,fx) ,@args)]

      [_ (pretty-print ast)
	 (error 'T-cps-err)]))

  (match ast
    [`(def ((ref ,fx) ,param ...) ,body)
     (define body+ (T-cps body fx))
     `((def ((ref ,fx) ,@param) ,body+) ,@lifted-defs)]

    [`(let ,lhs ,(and rhs (or `(const ,_) `(object ,_ ...))))
     `(let ,lhs ,rhs)]
    
    [`(let ,lhs ,rhs)
     (error 'let-cps-not-fully-supported)]

    [_ (pretty-print ast) (error 'cps-convert-err)]))


(define (simplify-module mod) 

  (define (lower-stmt ast [return-var #f]) 
    (define (recur ast) (lower-stmt ast return-var))
    ;; Flattens CPS code into basic-blocks of blessed 
    (match ast

      ;; Assignment to fresh immutable var
      [`(let (ref ,x) (bless ,rhs) ,body)
       `(((ref =) (ref ,x) ,rhs)
	 ,@(recur body))]

      [`(let (ref ,x) ,(and rhs (or `(const ,_) `(ref ,_))) ,body)
       `(((ref =) (ref ,x) ,rhs)
	 ,@(recur body))]

      [`(let (ref ,x) (subword (ref ,tag) ,e0) ,body)
       `(((ref =) (ref ,x)
	  ((ref box_subword) ((ref unbox_subword) ,e0) (ref ,tag)))
	 ,@(recur body))]

      [`(let (ref ,x) (object (ref ,tag) ,es ...) ,body)
       (define rx (gensymb 'a))
       `(((ref =) ((ref |!|) (ref ,rx))
	  ((ref alloc) (const ,(+ 1 (length es)))))
	 (do ((ref init_obj) (ref ,rx) (const 0)
	      ((ref obj_head_word)
	       (const ,(length es))
	       (ref ,(sym-append tag "_vtable")))))
	 ,@(map (lambda (ae i)
		  `(do ((ref init_obj) (ref ,rx) (const ,i) ,ae)))
		es
		(range 1 (add1 (length es))))
	 ((ref =) (ref ,x) ((ref u64bit_or) ((ref freeze) (ref ,rx)) (const 1)))
	 ,@(recur body))]

      ;; Lower List/Slice Literals
      [`(let (ref ,x) (|[]| ,es ...) ,body)
       (define (make-chunk-ast target-x elems)
         (define rx (gensymb 'sl_chk))
         ;; Alloc len + 1 for header-zero at front
         `(((ref =) ((ref |!|) (ref ,rx)) ((ref alloc) (const ,(+ 1 (length elems)))))
           ;; Set the header at index 0 to 0 (NULL/None)
           (do ((ref init_obj) (ref ,rx) (const 0) (const 0)))
           ;; Fill elements starting at index 1
           ,@(for/list ([e elems] [i (in-naturals)])
               `(do ((ref init_obj) (ref ,rx) (const ,(+ 1 i)) ,e)))
           ((ref =) (ref ,target-x) ;; final value is (rx + 1) | 2
            ((ref u64bit_or)
	     ((ref plus) ((ref manys_t) ((ref freeze) (ref ,rx))) (const 1))
	     (const 2)))))

       (define (join-chunks ops)
         (match ops
           ['() `(((ref =) (ref ,x) (ref _empty)))] 
           [`((,_ ... ((ref =) (ref ,last-v) ,_)))
	    (append (first ops) `(((ref =) (ref ,x) (ref ,last-v))))]
           [`(,c1 ,c2 ,rest ...)
            (match-let ([`(,_ ... ((ref =) (ref ,v1) ,_)) c1]
                        [`(,_ ... ((ref =) (ref ,v2) ,_)) c2])
              (join-chunks (cons (append c1 c2 
					 `(((ref =) (ref ,(gensymb 'join)) 
					    ((ref +) (ref none) (ref ,v1) (ref ,v2)))))
				 rest)))]))

       (define-values (all-chunks last-chunk)
         (for/fold ([chunks '()] [curr-chunk '()]) ([e (in-list es)])
           (match e
             [`(,ell ,v) #:when (eq? ell '|...|) 
              (define chunk-ops
                (if (null? curr-chunk)
		    '()
                    (let ([tv (gensymb 'chk)])
                      (list (make-chunk-ast tv (reverse curr-chunk))))))
              (define splice-op 
                (let ([tv (gensymb 'spl)])
                  `(((ref =) (ref ,tv) ,v))))
              
              (values (append chunks chunk-ops (list splice-op)) '())]
             
             [_ (values chunks (cons e curr-chunk))])))

       (define final-chunks 
         (if (null? last-chunk) 
             all-chunks
             (let ([tv (gensymb 'last)])
               (append all-chunks (list (make-chunk-ast tv (reverse last-chunk)))))))
       
       (append (join-chunks final-chunks)
               (recur body))]

      ;; If is just if, but we start new basic blocks
      [`(let (ref ,x) (if ,g ,t ,e) ,body)
       (define x+ (gensymb x)) ;; lower in-place with x+ as mut join var
       `(,@(lower-stmt `(if ,g ,t ,e) x+)
	 ((ref =) (ref ,x) ((ref freeze) (ref ,x+)))
	 ,@(recur body))]
      [`(if ,g ,t ,e)
       (define g+ (gensymb 'grd))
       `(((ref =) (ref ,g+) ((ref eq) ,g (ref _false)))
	 (if (ref ,g+) ((ref |{}|) ,@(recur e)) ((ref |{}|) ,@(recur t))))]
      
      ;; Invoke fun-ptr at fallback ptr, then increment and pass fwd
      [`(continue-dispatch ,fallback ,args ...)
       (define fun (gensymb 'fallbackfun))
       (define fb1 (gensymb 'fallbk1_))
       (define rv (gensymb 'rv))
       `(((ref =) (ref ,fun) ((ref deref) ((ref anys_t) ,fallback))) 
         ((ref =) (ref ,fb1) ((ref plus) ((ref manys_t) ,fallback) (const 1)))
         (return ((ref ,fun) (ref ,fb1) ,@args)))]

      ;; Return to current continuation
      [`(return ,ae) #:when return-var ;; local var cont
       `(((ref =) ((ref |!|) (ref ,return-var)) ,ae))]
      [`(return ,ae)
       (define kfun (gensymb 'kfun)) ;; nonlocal stack cont
       `(((ref =) (ref ,kfun) ((ref stack_pop)))
	 (return ((ref ,kfun) (const 0) ,ae)))]
      
      ;; Emit a method call based on the _pos and _link variables
      [`((ref ,fx)) (error "Not yet supported: thunk call, no args")]
      [`((ref ,fx) ,arg0 ,args ...)
       `((return ((ref ,fx) ,arg0 ,@args)))]
      
      [_ (pretty-print ast)
	 (error "lower-ast: Unknown AST")]))
  
  (define (def->blessed ast)
    (match ast
      [`(def ((ref ,fx) ,args ...) ,body)
        `(blessed ((ref ,fx) ,@args) ((ref |{}|) ,@(lower-stmt body)))]))
  
  (set! global-names (set 'v_equal
                          '_u_0003d)) ; Unicode name for =
  (match mod
    [`(module ,name ,mtag ,bless ,inline ,blessed ,lets ,defs ,methods ,types)
     (set! reserved-bl-x
      (set-union reserved-bl-x
        (for/set ([(ast) (in-list inline)])
          (match ast [`(blessed ((ref ,fx) . ,_) ,_) fx]))))

     (define defs+	 ;; Simplify core code: Alpha -> ANF -> CPS 
       (foldr append '() ;; flatten (CPS may emit >1 def for each def)
	      (for/list ([ast defs]) 
          (cps-convert (anf-convert (alphatize ast))))))

     ;; Use helpers just above to lower these defs to blessed code
     `(module ,name ,mtag ,bless ,inline ,(append (map def->blessed defs+) blessed)
	      ,(for/list ([ast lets]) (anf-convert (alphatize ast)))
	      ,defs+
	      ,methods ,types)]))


