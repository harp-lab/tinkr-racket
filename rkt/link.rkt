#lang racket


(provide compile-link-module)


(require "utils.rkt"
	 racket/system
	 racket/hash
	 racket/runtime-path)


(define (compile-link-module build-root)
  ;; The include DAG (with clauses), written by setup-build-workspace
  (define graph-data
    (with-input-from-file (build-path build-root "graph.rktd") read))
  (define prelude-dir (cadr (assq 'prelude graph-data)))
  (define root-dir (cadr (assq 'root graph-data)))
  (define graph-edges ;; dir-name-string -> ((target-dir (clause ...) ...) ...)
    (for/hash ([m (in-list (cdr (assq 'modules graph-data)))])
      (values (car m) (cdr m))))

  ;; Friendly validation of include clauses: shapes, duplicates, unknown heads.
  (for ([(dir edges) (in-hash graph-edges)])
    (define seen-aliases (mutable-set))
    (for ([e (in-list edges)])
      (define seen-rename-targets (mutable-set))
      (for ([c (in-list (cdr e))])
        (match c
          [`(clause rename ,old ,new)
           (when (set-member? seen-rename-targets new)
             (eprintf "link warning: in module ~a, more than one name is renamed to '~a' on the same include (the first rename wins)\n"
                      dir new))
           (set-add! seen-rename-targets new)]
          [`(clause rename ,_ ...)
           (error 'link (format "malformed [rename ...] clause in module ~a: expected [rename <old> <new>], got [~a]"
                                dir (string-join (map ~a (cdr c)) " ")))]
          [`(clause except ,_ ...) (void)]
          [`(clause only ,_ ...) (void)]
          [`(clause as ,m)
           (when (set-member? seen-aliases m)
             (error 'link (format "duplicate module alias '~a' in module ~a: [as ~a] appears on more than one include" m dir m)))
           (set-add! seen-aliases m)]
          [`(clause as ,_ ...)
           (error 'link (format "malformed [as ...] clause in module ~a: expected exactly one alias name, e.g. [as m]" dir))]
          [`(clause ,h ,_ ...)
           (eprintf "link warning: unknown include clause [~a ...] in module ~a — known clauses are rename, except, only, as\n"
                    h dir)]))))

  ;; Per-module link metadata from each .bl (+ .globals sidecar)
  (define mod-infos ;; dir-name-string -> info hash
    (for/fold ([h (hash)])
              ([entry (in-list (directory-list build-root))]
               #:when (directory-exists? (build-path build-root entry)))
      (define subdir (build-path build-root entry))
      (define bl-files
        (filter (lambda (f) (path-has-extension? f ".bl"))
                (directory-list subdir)))
      (if (null? bl-files)
          h
          (match (with-input-from-file (build-path subdir (car bl-files)) read)
            [`(module ,name ,mtag ,bless ,inline ,blessed
                      ,lets ,defs ,methods ,types)
             (define globals-file
               (path-replace-extension (build-path subdir (car bl-files))
                                       ".used"))
             (hash-set h (~a name)
               (hash 'mtag mtag
                     'methods methods
                     'lets (for/list ([l (in-list lets)])
                             (match l [`(let (ref ,x) ,_) x]))
                     'globals (if (file-exists? globals-file)
                                  (with-input-from-file globals-file read)
                                  '())
                     'types types))]))))

  ;; Alphabetical module order (matches the old directory-list order)
  (define mod-dirs (sort (hash-keys mod-infos) string<?))

  (define tag-methods-types
    (for/list ([dir (in-list mod-dirs)])
      (define info (hash-ref mod-infos dir))
      (list (hash-ref info 'mtag) (hash-ref info 'methods)
            (hash-ref info 'types))))

  (define all-method-tags (map first tag-methods-types))
  (define all-method-maps (map second tag-methods-types))
  (define all-types (apply append (map third tag-methods-types)))
  (define subword-types (filter subword-tag? all-types))
  (define obj-types (filter (not/c subword-tag?) all-types))

  (define all-methods-ord
    (set->list
     (foldl set-union (set)
	    (for/list ([(tmt) (in-list tag-methods-types)])
		      (for/set ([(k v) (in-hash (make-hash (second tmt)))])
			       (car k))))))
  (define all-other-methods
    (foldl (lambda (new-map-ls acc-map)
	     (define new-map (make-hash new-map-ls))
             (define all-keys (set-union (list->set (hash-keys new-map))
					 (list->set (hash-keys acc-map))))
             (for/hash ([k (in-set all-keys)])
		       (define existing-list (hash-ref acc-map k '()))
		       (define new-item (hash-ref new-map k #f))
		       (values k
			       (if new-item
				   (cons new-item existing-list)
				   existing-list))))
           (hash)
           all-method-maps))
  (define all-obj-methods
    (foldl hash-union (hash)
	   (map (lambda (mp) ;; Rebuild without (cons name #f) and default methods
		  (for/hash ([(kv) (in-list mp)]
			     #:when (and (cdr (car kv))
					 (not (eq? 'default (cdr (car kv))))))
			    (values (car kv) (cdr kv))))
		all-method-maps)))
  (define method-obj-impl
    (for/hash ([(m) (in-set (list->set (map car (hash-keys all-obj-methods))))])
	      (values m (for/hash ([(k v) (in-hash all-obj-methods)]
				   #:when (equal? (car k) m))
				  (values (cdr k) v)))))
  
  ;; Generate decls/.h and defs/.cpp
  (define method-decls ;; each method gets a position and a link vector 
    (foldl string-append ""
	   (map (lambda (method)
		  (define method+ (escape-id-for-C method))
		  (string-append
		   (format "extern const u32 ~a_pos;\n" method+)
		   (format "extern reg_passing AVXRet ~a(~a);\n" method+
			   "many,many,many,any,any,any,any,any,any,any,any")
		   (format "extern const blessed_t ~a_link[];\n" method+)))
		all-methods-ord)))
  (define method-defs ;; pos is canonical in vtables, link is populated w/
    (foldl string-append "" ;; method defs for non-obj cases across modules
       (map (lambda (method i)
          (define method+ (escape-id-for-C method))
          (define impls
            (map (lambda (impl)
               (format "fn_to_blessed(~a)" (escape-id-for-C impl)))
             (append ;; guarded chains first, then trailing default chains
              (hash-ref all-other-methods (cons method #f) list)
              (hash-ref all-other-methods (cons method 'default) list))))
          (define std-arg "alloc_fr,alloc_bk,stack_fr")
          (define o-arg "a0,a1,a2,a3,a4,a5,a6")
          (define std-param
            "many alloc_fr, many alloc_bk, many stack_fr, any fb")
          (define o-param
            "any a0,any a1,any a2,any a3,any a4,any a5,any a6")
          (string-append
	   (format "reg_passing AVXRet fail_dispatch_~a(~a, ~a) {\n  return fatal(alloc_fr, alloc_bk, stack_fr, (any)\"Dispatch failed on method '~a'.\", (any)0, (any)0, (any)0, (any)0, (any)0, (any)0, (any)0);\n}\n" 
                   method+ std-param o-param method)           
           (format "const u32 ~a_pos = ~a;\n" method+ i)
           (format "const blessed_t ~a_link[] = {\n~a};\n" method+
               (if (null? impls)
                 (format "fn_to_blessed(fail_dispatch_~a)" method+)
                   (string-append
                (string-join impls ",\n    ")
              (format ",\n    fn_to_blessed(fail_dispatch_~a)" method+))))
           (format "reg_passing AVXRet ~a(~a, ~a)\n{\n~a~a~a}\n\n"
               method+ std-param o-param
               (format "  DBG(\"Method call to ~a (aka ~a): \" ~a);\n" method+ method
                   "<< \"(arg count: \" << DBG_VALUE_BASE10(a0) << \") \" << DBG_VALUE(a1) << \", \"<< DBG_VALUE(a2) << \", \"<< DBG_VALUE(a3) << \", \"<< DBG_VALUE(a4) << \", \"<< DBG_VALUE(a5) << \", \"<< DBG_VALUE(a6)")
               (format "  AVXRet r = vtable_lookup(~a,a1,(any)(u64)~a_pos,0,0,0,0,0,0);\n"
                   std-arg
                   method+)
               (format "  tailcall any_to_blessed(r.a0())(~a,~a_link,~a);\n"
                   std-arg
                   method+
                   o-arg))))
        all-methods-ord
        (range (length all-methods-ord)))))
  (define subword-decls
    (foldl string-append "extern const blessed_t* const subword_tables[];\n"
	   (map (lambda (typename)
		  (format "extern const u32 ~a;\n"
			  (escape-id-for-C typename)))
	        subword-types)))
  (define subword-defs
    (foldl string-append
	   (format "const blessed_t* const subword_tables[] = {\n~a};\n"
		   (string-join
		    (map (lambda (typename)
			   (format "(blessed_t*)&~a_vtable"
				   (escape-id-for-C typename)))
			 subword-types)
		    ",\n    ")) 
	   (map (lambda (typename i)
		  (format "const u32 ~a = ~a;\n"
			  (escape-id-for-C typename) i))
		subword-types
		(range (length subword-types)))))
  (define vtable-decls 
    (foldl string-append ""
	   (append
	    (map (lambda (type)
		   (format "extern blessed_t ~a_vtable[];\n"
			   (escape-id-for-C type)))
		 all-types)
	    (map (lambda (type)
		   (format "extern any ~a;\n" (escape-id-for-C type)))
		 obj-types))))
  (define vtable-defs
    (foldl string-append ""
	   (append
	    (map (lambda (type)
		   (format "blessed_t ~a_vtable[] = {\n~a};\n"
			   (escape-id-for-C type)
			   (string-join
			    (map (lambda (method)
				   (define obj-h
				     (hash-ref method-obj-impl method hash))
				   (if (hash-has-key? obj-h type)
               (format "fn_to_blessed(~a)"
					       (escape-id-for-C
						(hash-ref obj-h type)))
               "fn_to_blessed(fail_locally)"))
				 all-methods-ord)
			    ",\n    ")))
		 all-types)
	    (map (lambda (type)
		   (format "any ~a = (any)~a_vtable;\n"
			   (escape-id-for-C type) (escape-id-for-C type)))
		 obj-types))))
  (define init-decls
    (string-append
     (format "extern reg_passing AVXRet entry_point_init(~a,~a);\n"
	     "many alloc_fr, many alloc_bk, many stack_fr"
	     "any a0, any a1, any a2, any a3, any a4, any a5, any a6, any a7")))
  (define init-defs
    (string-append
     (format "reg_passing AVXRet _main_shim(~a, ~a)\n{\n  tailcall _main(alloc_fr, alloc_bk, stack_fr, (any)0, (any)0, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg);\n}\n"
             "many alloc_fr, many alloc_bk, many stack_fr"
             "any a0, any a1, any a2, any a3, any a4, any a5, any a6, any a7")
     (format "reg_passing AVXRet entry_point_init(~a,~a)\n{\n AVXRet r;\n~a~a~a~a}\n"
         "many alloc_fr, many alloc_bk, many stack_fr"
         "any a0, any a1, any a2, any a3, any a4, any a5, any a6, any a7"
         " stack_store_blessed(stack_fr, 0, _main_shim);\n"  ;; <-- PUSH SHIM HERE
         (apply string-append
            (map (lambda (mtag i)
             (format " stack_store_blessed(stack_fr, ~a, ~a);\n"
                   i
                   (format "_entry__point__~a" mtag)))
             all-method-tags
             (range 1 (add1 (length all-method-tags)))))
         (format " stack_fr = (many)((many*)stack_fr + ~a);\n"
             (length all-method-tags))
         (format " tailcall stack_load_blessed(stack_fr, 0)(~a,~a);\n"
             "alloc_fr,alloc_bk,stack_fr,(any)0,(any)0"
             "(any)0,(any)0,(any)0,(any)0,(any)0,(any)0"))))
  
  ;; ---------------- Per-module views ----------------
  ;; Every module's free names were qualified to mv_<dir>__<name> at .cpp
  ;; emission. Here we decide what each of those symbols means: a per-module
  ;; view dispatcher over the include DAG, an alias to a top-level let, or a
  ;; shim to a global blessed C function.

  ;; Map from C-escaped spelling back to the raw name: method names, plus
  ;; local spellings introduced by rename clauses (which may name something
  ;; that exists nowhere under that spelling).
  (define escaped->raw
    (let ([h (for*/fold ([h (hash)])
                        ([dir (in-list mod-dirs)]
                         [mkv (in-list (hash-ref (hash-ref mod-infos dir) 'methods))])
               (hash-set h (escape-id-for-C (car (car mkv))) (car (car mkv))))])
      (for*/fold ([h h])
                 ([(dir edges) (in-hash graph-edges)]
                  [e (in-list edges)]
                  [c (in-list (cdr e))]
                  #:when (eq? (cadr c) 'rename)) ;; (clause rename old new)
        (hash-set h (escape-id-for-C (cadddr c)) (cadddr c)))))

  (define all-let-names
    (for*/set ([dir (in-list mod-dirs)]
               [x (in-list (hash-ref (hash-ref mod-infos dir) 'lets))])
      x))

  ;; Names with receiver (object/subword) methods anywhere: these dispatch
  ;; through vtable rows, so an empty chain view is not suspicious.
  (define obj-method-names
    (for*/set ([dir (in-list mod-dirs)]
               [mkv (in-list (hash-ref (hash-ref mod-infos dir) 'methods))]
               #:when (and (cdr (car mkv))
                           (not (eq? 'default (cdr (car mkv))))))
      (car (car mkv))))

  ;; The chain head published by module `dir` for name `n`;
  ;; `key` is #f (guarded chain) or 'default (trailing default chain)
  (define (chain-of dir n key)
    (define info (hash-ref mod-infos dir #f))
    (define kv (and info (assoc (cons n key) (hash-ref info 'methods))))
    (and kv (cdr kv)))

  ;; Given the name `spelled` as the includer spells it, the corresponding
  ;; spelling in the include target, or #f if the name is not imported.
  ;; An explicit rename imports unconditionally; otherwise the name must
  ;; survive except/only filters and must not have been renamed away.
  (define (resolve-spelling spelled clauses)
    (define cs (map cdr clauses)) ;; strip the 'clause tag
    (define renames (for/list ([c (in-list cs)] #:when (eq? (car c) 'rename)) c))
    (define hit (for/first ([c (in-list renames)]
                            #:when (eq? (caddr c) spelled))
                  (cadr c)))
    (define renamed-olds (map cadr renames))
    (define excepts (for*/list ([c (in-list cs)] #:when (eq? (car c) 'except)
                                [x (in-list (cdr c))]) x))
    (define onlys (for*/list ([c (in-list cs)] #:when (eq? (car c) 'only)
                              [x (in-list (cdr c))]) x))
    ;; The presence of any [only ...] clause activates the whitelist, even
    ;; an empty one: include "m.ti" [only] [as m] merges nothing unqualified.
    (define has-only? (for/or ([c (in-list cs)]) (eq? (car c) 'only)))
    (cond [hit hit]
          [(memq spelled renamed-olds) #f]
          [(memq spelled excepts) #f]
          [(and has-only? (not (memq spelled onlys))) #f]
          [else spelled]))

  ;; Clause semantics for qualified (alias.name) references: renames define
  ;; the spelling vocabulary and apply to both access paths, but except/only
  ;; curate only the unqualified merge — an alias is a full window onto the
  ;; target's view under the edge's renames.
  (define (resolve-spelling/qualified spelled clauses)
    (define cs (map cdr clauses))
    (define renames (for/list ([c (in-list cs)] #:when (eq? (car c) 'rename)) c))
    (define hit (for/first ([c (in-list renames)]
                            #:when (eq? (caddr c) spelled))
                  (cadr c)))
    (cond [hit hit]
          [(memq spelled (map cadr renames)) #f] ;; renamed away
          [else spelled]))

  ;; ---- Qualified references: mv_<dir>___m_0002ex came from m.x ----
  ;; escape-id-for-C renders '.' as _0002e, which no source identifier can
  ;; produce (a literal '_' always escapes to '__'), so splitting on the
  ;; first occurrence is unambiguous.
  (define (split-qualified g)
    (define s (symbol->string g))
    (define p (regexp-match-positions #rx"_0002e" s))
    (and p (cons (substring s 0 (caar p)) (substring s (cdar p)))))

  ;; Inverts escape-id-for-C on a suffix (a tail never carries the _/_u
  ;; prefix): __ -> _, _XXXXX (five hex digits) -> that character.
  (define (unescape-tail s)
    (let loop ([cs (string->list s)] [acc '()])
      (match cs
        ['() (string->symbol (list->string (reverse acc)))]
        [(list* #\_ #\_ r) (loop r (cons #\_ acc))]
        [(list* #\_ h1 h2 h3 h4 h5 r)
         (loop r (cons (integer->char (string->number (string h1 h2 h3 h4 h5) 16))
                       acc))]
        [(cons c r) (loop r (cons c acc))])))

  (define dir-aliases ;; dir -> (alias -> include edge)
    (for/hash ([(dir edges) (in-hash graph-edges)])
      (values dir
              (for*/fold ([h (hash)])
                         ([e (in-list edges)]
                          [c (in-list (cdr e))])
                (match c
                  [`(clause as ,m) (hash-set h m e)]
                  [_ h])))))

  ;; Does module `dir` register any receiver (object/subword) method under
  ;; spelling `s`? If so, a view passing through `dir` must probe `s`'s row.
  (define (dir-has-obj-method? dir s)
    (for/or ([mkv (in-list (hash-ref (hash-ref mod-infos dir) 'methods))])
      (and (equal? (car (car mkv)) s)
           (cdr (car mkv))
           (not (eq? 'default (cdr (car mkv)))))))

  ;; The ordered dispatch view of raw name `n` from module `m`:
  ;; a guarded band of events ((probe . spelling) | (chain . head)) and a
  ;; default band of chain heads. Preorder DFS over include edges, first
  ;; occurrence wins, with an implicit prelude (base.ti) edge last.
  ;; A probe event is placed at the first module providing each distinct
  ;; spelling, so receiver methods are checked before that segment's chains.
  (define (compute-view m n)
    (define visited (mutable-set))
    (define probed (mutable-set))
    (define events '())
    (define defaults '())
    (define (visit dir spelled)
      (unless (or (set-member? visited (cons dir spelled))
                  (not (hash-has-key? mod-infos dir)))
        (set-add! visited (cons dir spelled))
        (define g (chain-of dir spelled #f))
        (when (and (not (set-member? probed spelled))
                   (or g (dir-has-obj-method? dir spelled)))
          (set-add! probed spelled)
          (set! events (cons (cons 'probe spelled) events)))
        (when g (set! events (cons (cons 'chain g) events)))
        (let ([d (chain-of dir spelled 'default)])
          (when d (set! defaults (cons d defaults))))
        (for ([e (in-list (hash-ref graph-edges dir '()))])
          (define spelled+ (resolve-spelling spelled (cdr e)))
          (when spelled+ (visit (car e) spelled+)))))
    (visit m n)
    (visit prelude-dir n)
    ;; Receiver methods travel with values: if this name has object methods
    ;; anywhere in the program but no probe was placed, probe it up front.
    (values (if (and (set-member? obj-method-names n)
                     (not (set-member? probed n)))
                (cons (cons 'probe n) (reverse events))
                (reverse events))
            (reverse defaults)))

  ;; Emission of view dispatchers, shims, aliases, and recheck thunks
  (define view-decls '())
  (define view-defs '())
  (define (emit-decl! s) (set! view-decls (cons s view-decls)))
  (define (emit-def! s) (set! view-defs (cons s view-defs)))
  (define needed-rechecks (mutable-set))

  (define vw-std-param "many alloc_fr, many alloc_bk, many stack_fr, any fb")
  (define vw-o-param "any a0,any a1,any a2,any a3,any a4,any a5,any a6")
  (define vw-std-arg "alloc_fr,alloc_bk,stack_fr")
  (define vw-o-arg "a0,a1,a2,a3,a4,a5,a6")
  (define vw-extern-sig "many,many,many,any,any,any,any,any,any,any,any")

  ;; Rename-introduced spellings need their own fail_dispatch (the union
  ;; only emits one per method name).
  (define extra-fail-names (mutable-set))

  (define (emit-shim! sym target)
    (emit-decl! (format "extern reg_passing AVXRet ~a(~a);\n" sym vw-extern-sig))
    (emit-def!
     (format "reg_passing AVXRet ~a(~a, ~a)\n{\n  tailcall ((blessed_t)~a)(~a,fb,~a);\n}\n"
             sym vw-std-param vw-o-param target vw-std-arg vw-o-arg)))

  (define (emit-let-alias! sym target)
    (emit-decl! (format "extern const void* const& ~a;\n" sym))
    (emit-def! (format "const void* const& ~a = ~a;\n" sym target)))

  ;; A view dispatcher is a pure walker over its link array: probe events
  ;; (vtable checks for a spelling's row) and chain heads, in view order,
  ;; guarded band then default band, ending in fail_dispatch for the name
  ;; whose fail message we want. Entering the dispatcher calls the first
  ;; entry with the rest of the array as its fallback.
  (define (emit-view-dispatcher! sym n events dseg)
    (define n+ (escape-id-for-C n))
    (unless (member n all-methods-ord)
      (set-add! extra-fail-names n))
    (define entries '())
    (for ([ev (in-list events)])
      (match ev
        [(cons 'probe spelling)
         (set-add! needed-rechecks spelling)
         (set! entries (cons (format "(blessed_t)recheck_~a"
                                     (escape-id-for-C spelling))
                             entries))]
        [(cons 'chain impl)
         (set! entries (cons (format "(blessed_t)~a" (escape-id-for-C impl))
                             entries))]))
    (for ([impl (in-list dseg)])
      (set! entries (cons (format "(blessed_t)~a" (escape-id-for-C impl))
                          entries)))
    (set! entries (cons (format "(blessed_t)fail_dispatch_~a" n+) entries))
    (emit-decl!
     (format "extern reg_passing AVXRet ~a(~a);\nextern const blessed_t ~a_link[];\n"
             sym vw-extern-sig sym))
    (emit-def!
     (string-append
      (format "const blessed_t ~a_link[] = {\n    ~a};\n" sym
              (string-join (reverse entries) ",\n    "))
      (format "reg_passing AVXRet ~a(~a, ~a)\n{\n  tailcall ((blessed_t)~a_link[0])(~a,(any)(~a_link+1),~a);\n}\n"
              sym vw-std-param vw-o-param sym vw-std-arg sym vw-o-arg))))

  ;; One symbol per (module, free name)
  (for ([dir (in-list mod-dirs)])
    (define info (hash-ref mod-infos dir))
    (for ([g (in-list (hash-ref info 'globals))]
          #:unless (memq g '(v_equal _u_0003d)))
      (define sym (format "mv_~a__~a" dir g))
      ;; A qualified reference alias.x: match the escaped prefix against this
      ;; module's aliases (a lookalike name with no matching alias falls
      ;; through to the ordinary path).
      (define qual
        (let ([q (split-qualified g)])
          (and q
               (for/first ([(m e) (in-hash (hash-ref dir-aliases dir (hash)))]
                           #:when (equal? (symbol->string (escape-id-for-C m))
                                          (car q)))
                 (list m e (unescape-tail (cdr q)))))))
      (define n (and (not qual) (hash-ref escaped->raw g #f)))
      (cond
        [qual
         (match-define (list m e raw-x) qual)
         (define dotted (string->symbol (format "~a.~a" m raw-x)))
         (define spelled (resolve-spelling/qualified raw-x (cdr e)))
         (cond
           [(not spelled)
            (eprintf "link warning: qualified reference ~a in module ~a names a spelling that include renames away\n"
                     dotted dir)
            (emit-view-dispatcher! sym dotted '() '())]
           [(hash-has-key? escaped->raw (escape-id-for-C spelled))
            (define-values (events dseg) (compute-view (car e) spelled))
            (when (and (null? events) (null? dseg))
              (eprintf "link warning: module ~a references ~a but no definition of '~a' is visible from '~a's includes\n"
                       dir dotted spelled m))
            (emit-view-dispatcher! sym dotted events dseg)]
           [(set-member? all-let-names spelled)
            (emit-let-alias! sym (escape-id-for-C spelled))]
           [else ;; a blessed C function (global by name)
            (emit-shim! sym (escape-id-for-C spelled))])]
        [n
         (define-values (events dseg) (compute-view dir n))
         (when (and (null? events) (null? dseg))
           (eprintf "link warning: module ~a references '~a' but no definition is visible from its includes\n"
                    dir n))
         (emit-view-dispatcher! sym n events dseg)]
        [(set-member? all-let-names g)
         (emit-let-alias! sym g)]
        [else ;; a blessed C function (global by name)
         (emit-shim! sym g)])))

  ;; Fail handlers for spellings that are not method names anywhere
  (for ([n (in-set extra-fail-names)])
    (define n+ (escape-id-for-C n))
    (emit-decl! (format "extern reg_passing AVXRet fail_dispatch_~a(~a);\n"
                        n+ vw-extern-sig))
    (emit-def!
     (format "reg_passing AVXRet fail_dispatch_~a(~a, ~a) {\n  return fatal(alloc_fr, alloc_bk, stack_fr, (any)\"Dispatch failed on method '~a'.\", (any)0, (any)0, (any)0, (any)0, (any)0, (any)0, (any)0);\n}\n"
             n+ vw-std-param vw-o-param n)))

  ;; Mid-chain vtable probes: one per foreign spelling used by any view
  (for ([s (in-set needed-rechecks)])
    (define s+ (escape-id-for-C s))
    (emit-decl! (format "extern reg_passing AVXRet recheck_~a(~a);\n" s+ vw-extern-sig))
    (emit-def!
     (format "reg_passing AVXRet recheck_~a(~a, ~a)\n{\n  AVXRet r = vtable_lookup(~a,a1,(any)(u64)~a_pos,0,0,0,0,0,0);\n  tailcall ((blessed_t)r.a0())(~a,fb,~a);\n}\n"
             s+ vw-std-param vw-o-param vw-std-arg s+ vw-std-arg vw-o-arg)))

  ;; Write out a link/ module within the build/X/ folder
  (define init-root (build-path build-root "link/"))
  (when (directory-exists? init-root)
    (delete-directory/files init-root))
  (make-directory* init-root)
  (with-output-to-file
      (build-path init-root "link.h")
    (lambda ()
      (display subword-decls) (display method-decls)
      (display vtable-decls) (display init-decls)
      (display (apply string-append (reverse view-decls))))
    #:exists 'replace)
  (with-output-to-file
      (build-path init-root "link.cpp")
    (lambda () (display "#include \"link.h\"\n")
	    (display subword-defs) (display method-defs)
	    (display vtable-defs) (display init-defs)
	    (display (apply string-append (reverse view-defs))))
    #:exists 'replace))


