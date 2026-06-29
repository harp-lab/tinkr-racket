#lang racket


(provide compile-link-module)


(require "utils.rkt"
	 racket/system
	 racket/hash
	 racket/runtime-path)


(define (compile-link-module build-root)
  (define tag-methods-types
    (apply ;; gather a list of triples, one per .bl file
     append ;; a module tag, a list-hash of methods, a list of type tags   
     (for/list
      ([entry (in-list (directory-list build-root))]
       #:when (directory-exists? (build-path build-root entry)))
      (define subdir (build-path build-root entry))
      ;; Find all .bl files in this specific subdirectory
      (define bl-files 
	(filter (lambda (f) (path-has-extension? f ".bl"))
		(directory-list subdir)))
      ;; Gather all let decls from this directory
      (apply append 
	     (map (lambda (bl)
		    (match (with-input-from-file (build-path subdir bl) read)
		      [`(module ,name ,mtag ,bless ,inline ,blessed
				,lets ,defs ,methods ,types)
		       `((,mtag ,methods ,types))]))
		  bl-files)))))

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
	   (map (lambda (mp) ;; Rebuild without (cons name #f) methods
		  (for/hash ([(kv) (in-list mp)] #:when (cdr (car kv)))
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
               (format "(blessed_t)~a" (escape-id-for-C impl)))
             (hash-ref all-other-methods (cons method #f) list)))
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
                   (format "(blessed_t)fail_dispatch_~a" method+)
                   (string-append
                (string-join impls ",\n    ")
                (format ",\n    (blessed_t)fail_dispatch_~a" method+))))
           (format "reg_passing AVXRet ~a(~a, ~a)\n{\n~a~a~a}\n\n"
               method+ std-param o-param
               (format "  DBG(\"Method call to ~a (aka ~a): \" ~a);\n" method+ method
                   "<< DBG_VALUE(a0) << \", \" << DBG_VALUE(a1) << \", \"<< DBG_VALUE(a2) << \", \"<< DBG_VALUE(a3) << \", \"<< DBG_VALUE(a4) << \", \"<< DBG_VALUE(a5) << \", \"<< DBG_VALUE(a6)")
               (format "  AVXRet r = vtable_lookup(~a,a0,(any)(u64)~a_pos,0,0,0,0,0,0);\n"
                   std-arg
                   method+)
               (format "  tailcall ~a(~a,~a_link,~a);\n"
                   "((blessed_t)r.a0())"
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
				       (format "(blessed_t)~a"
					       (escape-id-for-C
						(hash-ref obj-h type)))
				       "(blessed_t)fail_locally"))
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
     (format "reg_passing AVXRet _main_shim(~a, ~a)\n{\n  tailcall _main(alloc_fr, alloc_bk, stack_fr, (any)0, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg, (any)_u__noarg);\n}\n"
             "many alloc_fr, many alloc_bk, many stack_fr"
             "any a0, any a1, any a2, any a3, any a4, any a5, any a6, any a7")
     (format "reg_passing AVXRet entry_point_init(~a,~a)\n{\n AVXRet r;\n~a~a~a~a}\n"
         "many alloc_fr, many alloc_bk, many stack_fr"
         "any a0, any a1, any a2, any a3, any a4, any a5, any a6, any a7"
         " ((many*)stack_fr)[0] = (many)(blessed_t)_main_shim;\n"  ;; <-- PUSH SHIM HERE
         (apply string-append
            (map (lambda (mtag i)
               (format " ((many*)stack_fr)[~a] = (many)(blessed_t)~a;\n"
                   i
                   (format "_entry__point__~a" mtag)))
             all-method-tags
             (range 1 (add1 (length all-method-tags)))))
         (format " stack_fr = (many)((many*)stack_fr + ~a);\n"
             (length all-method-tags))
         (format " tailcall ((blessed_t)*(many*)stack_fr)(~a,~a);\n"
             "alloc_fr,alloc_bk,stack_fr,(any)0,(any)0"
             "(any)0,(any)0,(any)0,(any)0,(any)0,(any)0"))))
  
  ;; Write out a link/ module within the build/X/ folder
  (define init-root (build-path build-root "link/"))
  (when (directory-exists? init-root)
    (delete-directory/files init-root))
  (make-directory* init-root)
  (with-output-to-file
      (build-path init-root "link.h")
    (lambda ()
      (display subword-decls) (display method-decls)
      (display vtable-decls) (display init-decls))
    #:exists 'replace)
  (with-output-to-file
      (build-path init-root "link.cpp")
    (lambda () (display "#include \"link.h\"\n")
	    (display subword-defs) (display method-defs)
	    (display vtable-defs) (display init-defs))
    #:exists 'replace))


