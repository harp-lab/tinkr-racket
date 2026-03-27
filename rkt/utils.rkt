#lang racket


(require "lexer.rkt")
(require "parser.rkt")

(require racket/runtime-path)
(require racket/system racket/file)

(provide gensymb
	 sym-append
	 subword-tag?
	 indent-string
	 small-expr?
	 size-expr-pred
	 print-ast
	 string->c-string
	 escape-id-for-C
	 escape-atom-for-C
	 bless-format
	 bless-arg-count
	 std-entry-path
	 build-clang!
	 build-cpp!
	 pad-params
	 pad-args)


(define std-entry-path "std/base.ti")

(define nums-pool "0123456789")
(define alpha-pool "abcdefghijklmnopqrstuvwxyz")
(define alphanum-pool (string-append nums-pool alpha-pool (string-upcase alpha-pool)))
(define seen-symb (make-hash))
(define (gensymb [s "gx"])
  (define (add s n pool)
	  (define randlst (shuffle (string->list (string-append pool pool pool))))
	  (string-append s (list->string (take randlst n))))
  (if (symbol? s) ;; start by alternating nums <--> alpha
      (gensymb (symbol->string s))
      (let ([s (if (string-contains?
		    nums-pool  (substring s (- (string-length s) 1)))
		   (add s 1 alpha-pool)
		   (add s 1 nums-pool))])
	(define symb ;; add 2+ more random chars
	  (let loop ([s (add s 2 alphanum-pool)])
	    (if (hash-has-key? seen-symb s)
		(loop (add s 1 alphanum-pool))
		s)))
	(hash-set! seen-symb symb #t)
	(string->symbol symb))))

(define (sym-append s0 s1 . lst)
  (if (null? lst)
      (if (string? s0)
	  (if (string? s1)
	      (string->symbol (string-append s0 s1))
	      (sym-append s0 (symbol->string s1)))
	  (sym-append (symbol->string s0) s1))
      (sym-append s0 (apply sym-append s1 (car lst) (cdr lst)))))

(define (get-arg n args)
  (if (< n (length args)) (~a (list-ref args n)) (error "bless format: no arg ~a" n)))

(define (bless-format fmt args)
  (string-join
   (let loop ([chars (string->list fmt)])
     (match chars
       [(list* #\$ (? char-numeric? d) rest)
        (cons (get-arg (- (char->integer d) 48) args) (loop rest))]
       [(cons c rest) (cons (string c) (loop rest))]
       ['() '()])) ""))

(define ((size-expr-pred sz) ast) 
  (if (< sz 0)
      #f
      (match ast
	[(cons e0 es)
	 (define rem ((size-expr-pred sz) e0))
	 (and rem ((size-expr-pred rem) es))]
	[_ (- sz 1)])))
(define small-expr? (size-expr-pred 150))

(define (escape-atom-for-C atom-e)
  (match atom-e
    [`(ref ,x) (escape-id-for-C x)]
    [`(const ,(? integer? v)) (number->string v)]
    [(? symbol? x) (escape-id-for-C x)]))

(define (escape-id-for-C x)
  (define s (if (symbol? x) (symbol->string x) x))
  (define s-list
    (for/list ([c (in-string s)]
	       [i (in-naturals)])
	      (match c
		[#\_ "__"]
		[(? char-numeric?) 
		 (if (= i 0)
		     (string-append "_"
				    (~r (char->integer c) #:base 16 #:min-width 5 #:pad-string "0"))
		     (string c))]
		[(? char-alphabetic?) (string c)]
		[_ (string-append "_"
				  (~r (char->integer c) #:base 16 #:min-width 5 #:pad-string "0"))])))
  (string->symbol
   (apply string-append
	  `(,(if (string-contains? alphanum-pool (car s-list)) "_" "_u") ,@s-list))))


(define (string->c-string s)
  (string-append
   "\""
   (apply string-append
          (for/list ([b (in-bytes (string->bytes/utf-8 s))])
		    (cond
		     ;; Standard C escapes for readability
		     [(= b 92) "\\\\"] ;; Backslash
		     [(= b 34) "\\\""] ;; Quote
		     [(= b 10) "\\n"]  ;; Newline
		     [(= b 13) "\\r"]  ;; CR
		     [(= b 9)  "\\t"]  ;; Tab
		     
		     ;; Printable ASCII (32-126) is safe to pass through raw
		     [(and (>= b 32) (<= b 126)) 
		      (string (integer->char b))]
		     
		     ;; Everything else (Unicode bytes, control chars):
		     ;; Escape as fixed-width Octal (\ooo).
		     ;; This guarantees the C++ compiler sees the exact UTF-8 byte sequence
		     ;; regardless of the source file encoding or compiler flags.
		     [else 
		      (format "\\~a" (~r b #:base 8 #:min-width 3 #:pad-string "0"))])))
   "\""))



(define (subword-tag? tag)
  (string-suffix? (symbol->string tag) "subword"))


;; Pretty-printing of C for the original code to make output easier to read
(define (indent-string s)
  (string-join (map (lambda (x) (string-append "  " x)) (string-split s "\n"))
	       "\n" #:after-last "\n"))

(define (print-ast ast)
  (define long
    (match ast
      [`(ref ,x) (format "~a\n" x)]
      [`(const ,c) (format "~v\n" c)]
      
      [`(def (,name ,args ...) ,body)
       (format "def (~a)\n~a\n"
               (string-join (map print-ast (cons name args)) " ")
               (indent-string (print-ast body)))]

      [`(blessed (,name ,args ...) ,body)
       (format "blessed (~a)\n~a\n"
               (string-join (map print-ast (cons name args)) " ")
               (indent-string (print-ast body)))]

      [`(let ,lhs ,rhs ,body)
       (define decl (format "let ~a = ~a" (print-ast lhs) (print-ast rhs)))
       (define rest 
	 (match body
           ;; If body is another let, don't indent (linear look)
           [`(let . ,_) (print-ast body)]
           ;; If body is the final return, indent it
           [_ (indent-string (print-ast body))]))
       (format "~a\n~a\n" decl rest)]

      [`(let ,lhs ,rhs)
       (format "let ~a = ~a\n" (print-ast lhs) (print-ast rhs))]

      [`(bless ,blessed-e) (format "bless ~a" blessed-e)]
      [`((const ,(? string? s)) ,args ...)
       (format "(~a)" (string-join (cons (format "~v" s) (map print-ast args)) " "))]
      
      [`(if ,g ,t ,e)
       (define g-s (print-ast g))
       (define t-s (indent-string (print-ast t)))
       (define e-s (indent-string (print-ast e)))
       (format "if ~a\n~a\n~a\n" g-s t-s e-s)]
      
      [`(object ,tag ,args ...)
       (format "`[~a]\n" (string-join (map print-ast (cons tag args)) " "))]
      [`(subword ,tag ,args ...)
       (format "`[[~a]]\n" (string-join (map print-ast (cons tag args)) " "))]

      [`(superjump ,args ...)
       (format "(superjump ~a)\n" (string-join (map print-ast args) " "))]
      
      [`(,f ,args ...)
       (format "(~a)\n" (string-join (map print-ast (cons f args)) " "))]

      [_ (format "~a\n" ast)]))

  (define long+ (regexp-replace* #px"[\n]+" (regexp-replace* #px"[ ]+" long " ") "\n"))
  
  (define short (string-trim (regexp-replace* #px"\\s+" long+ " ")))
  
  (if (< (string-length short) 29) short long))


(define (build-clang! prog-str)
  (define build-dir "build")

  (when (directory-exists? build-dir)
    (delete-directory/files build-dir))
  (make-directory build-dir)
  
  (display-to-file (string-append prog-str
				  (with-input-from-file
				    "std/main.cpp"
				    (lambda () (read-string 49999))))
		   "build/prog.cpp"
		   #:exists 'replace)

  (build-cpp! "build/prog.cpp"))


(define (build-cpp! cpp-path
                    [bin-path (normalize-path "build/out.bin")]
                    [cxx-path (find-executable-path "c++")])
  
  (unless cxx-path
    (error "Error: C++ has not been found in PATH."))

  (let ()
    (define-values (sp out in err)
    (subprocess
     #f
     #f	;; for some reason ld fails doing it this way
     #f	;; but otherwise I can build it manually this way
     cxx-path
     cpp-path
     "-g"
     "-lgmp"
     "-lgc"
     "-march=native"
     "-ferror-limit=3"
     ;;"-fmax-errors=1"
     "-std=c++20"
     (format "-o~a" bin-path)))
  (let loop () ;; echo (debug) output from daemon
    (define s (read-line err))
    (when (not (eof-object? s))
      (display s)
      (newline)
      (loop)))
  (close-input-port out)
  (close-output-port in)
  (close-input-port err)
  (subprocess-wait sp)
  (when (> (subprocess-status sp) 0)
    (error "Something went wrong running c++!")))
  
  (let ()
    (define-values (sp out in err)
    (subprocess
     #f
     #f	;; for some reason ld fails doing it this way
     #f	;; but otherwise I can build it manually this way
     cxx-path
     cpp-path
     "-O3"
     "-S"
     "-emit-llvm"
     "-march=native"
     "-ferror-limit=3"
     "-std=c++20"
     "-o./build/prog.ll"))
  (let loop () ;; echo (debug) output from daemon
    (define s (read-line err))
    (when (not (eof-object? s))
      (display s)
      (newline)
      (loop)))
  (close-input-port out)
  (close-output-port in)
  (close-input-port err)
  (subprocess-wait sp)
  (when (> (subprocess-status sp) 0)
    (error "Something went wrong generating llvm ir!")))

  bin-path)


(define bless-arg-count 8)

(define (pad-args sofar)
  (if (>= sofar bless-arg-count)
      '()
      (cons `(ref _u__noarg) (pad-args (add1 sofar)))))

(define (pad-params sofar)
  (if (>= sofar bless-arg-count)
      '()
      (cons `(ref ,(gensymb '_)) (pad-params (add1 sofar)))))
