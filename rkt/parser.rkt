#lang racket

(provide parse-port
         parse-file
         strip-prov
         verbose-print-ast
         syn->filename)

(require "lexer.rkt")

(define (syn->filename ast)
  (match ast
    [`(syn (src ,file ,_ ...) ,_ ...) file]
    [_ (error "Cannot lookup filename for syntax.")]))

(define (whitespace n)
  (if (= n 0)
      ""
      (string-append " " (whitespace (- n 1)))))

(define current-toks '())
(define current-lex '())
(define (peek [i 0])
  (if (> (length current-toks) i)
      (list-ref current-toks i)
      (let ([more (list (current-lex) (current-lex) (current-lex))])
	(set! current-toks (append current-toks more))
	(peek i))))

;; Global state to track the end of the most recently parsed segment
(define last-consumed-tok #f)

(define (advance [i 0])
  (if (> i 0)
      (begin (advance 0) (advance (- i 1)))
      (let ([start-tok (peek 0)])
	(set! last-consumed-tok start-tok)
	(peek i) 
	(set! current-toks (drop current-toks (+ 1 i)))
	(void))))

(define (expect str)
  ; expects a token and advances toks
  (define str0 (token->str (peek)))
  (if (equal? str str0)
      (advance)
      (error (format "expected '~a' but got '~a' at line ~a of ~a"
		     str str0 (pos->startline (token->pos (peek))) (pos->file (token->pos (peek)))))))

(define (strip-prov e)
  ; strips provenance information from an AST
  (match e
    [`(module ,nm ,prov
        ,body)
     `(module ,nm ,(strip-prov body)
        )]
    [`(syn ,prov . ,e0) (strip-prov e0)]
    [(? list? e) (map strip-prov e)]
    [(? set? s) (list->set (map strip-prov (set->list s)))]
    ;(foldl (lambda (k h+) (hash-set h+ (strip-prov k) (strip-prov (hash-ref h k)))) (hash) (hash-keys h))
    [(? hash? h) `(hash: ,@(map strip-prov (hash-keys h)))]
    [_ e]))

(define (verbose-print-ast e)
  ; dumps a preorder traversal pretty-printing of an AST to STDOUT
  (match e
    [`(module ,name ,toks
        ,ast)
     (verbose-print-ast ast)]
    [`(syn (prov ,rest ...) const ,e0) (pretty-print e)]
    [`(syn (prov ,rest ...) ,tag ,es ...)
     (pretty-print `(syn (prov ,@rest) ,tag ,(map strip-prov es)))
     (void (map verbose-print-ast es))]))

(define (emit-expr expr start-tok)
  
  (define start-pos (token->pos start-tok))
  (define file (pos->file start-pos))
  (define sl (pos->startline start-pos))
  (define sc (pos->startcol start-pos))

  ;; last-consumed-tok is updated by advance so we have it
  (define end-tok (or last-consumed-tok start-tok))
  (define end-pos (token->pos end-tok))
  (define el (pos->endline end-pos))
  (define ec (pos->endcol end-pos))

  ;; add prov info to the syntax object
  `(syn (src ,file ,sl ,sc ,el ,ec) . ,expr))

(define (parse-small qd)
  ;; a small is just a quoted or unquoted atom
  ;; this is also the nonterminal used for the lhs of a let
  (define s-tok (peek))
  (match (token->str s-tok)
    ["`" (advance)
     (emit-expr `(,(emit-expr `(ref |`|) s-tok) ,(parse-small (+ qd 1))) s-tok)]
    ["," (advance)
     (emit-expr `(,(emit-expr `(ref |,|) s-tok) ,(parse-small (- qd 1))) s-tok)]
    [_ (parse-atom qd)]))

(define (parse-bracketed-then parser close-str k qd)
  (if (equal? close-str (token->str (peek)))
      (begin (advance) (k '()))
      (let ([e0 (parser qd)])
        (parse-bracketed-then parser close-str
			      (lambda (es) (k (cons e0 es)))
			      qd))))

(define (parse-atom qd) 
  (define start-tok (peek))
  (define tokstr (token->str start-tok))

  (if (and (hash-has-key? keywords tokstr) (< qd 1))
      (((hash-ref keywords tokstr) qd))
      (match (token->tag start-tok)
        [(or 'id 'ref) (advance)
         (emit-expr `(ref ,(string->symbol tokstr)) start-tok)]
        ['num (advance)
         (emit-expr `(const ,(string->number tokstr)) start-tok)]
        ['str (advance)
         (emit-expr `(const ,(substring tokstr 1 (sub1 (string-length tokstr)))) start-tok)]
        ['popen #:when (and (hash-has-key? keywords (token->str (peek 1))) (< qd 1))
         (advance)
         (begin0 (parse qd) (expect ")"))]
        ['popen #:when (equal? "ref" (token->str (peek 1)))
         (advance 1)
         (parse-bracketed-then parse ")"
			       (lambda (es) (emit-expr `(ref ,@es) start-tok)) qd)]
        ['popen #:when (eq? 'op (token->tag (peek 1)))
         (advance) 
         (let* ([op (peek)] [_ (advance)]
                [op-ref (emit-expr `(ref ,(string->symbol (token->str op))) op)])
           (parse-bracketed-then parse ")" (lambda (es) (emit-expr `(,op-ref . ,es) start-tok)) qd))]
        ['popen (advance)
         (parse-bracketed-then parse ")" (lambda (es) (emit-expr es start-tok)) qd)]
        ['copen (advance)
         (let ([ref-curly (emit-expr `(ref ,(string->symbol "{}")) start-tok)])
           (parse-bracketed-then parse "}" (lambda (es) (emit-expr `(,ref-curly . ,es) start-tok)) qd))]
        ['sopen (advance)
         (let ([ref-square (emit-expr `(ref ,(string->symbol "[]")) start-tok)])
           (parse-bracketed-then parse "]" (lambda (es) (emit-expr `(,ref-square . ,es) start-tok)) qd))]
        [_ (error (format "Expected an atom ~a" (list start-tok)))])))

; Identify the next quote depth from the current token and qd.
(define (next-qd qd)
  (match (token->str (peek))
    ["`" (+ qd 1)]
    ["," (- qd 1)]
    [_ qd]))

(define (parse-w-rem-operators-pre prefixes ops qd)
  (define start-tok (peek))
  (define tokstr (token->str start-tok))
  (if (set-member? prefixes tokstr)
      (begin (advance)
             (let ([op-ref (emit-expr `(ref ,(string->symbol tokstr)) start-tok)]
                   [e0 (parse-w-rem-operators ops (next-qd qd))])
               (emit-expr `(,op-ref ,e0) start-tok)))
      (parse-w-rem-operators (cdr ops) qd)))

(define (parse-w-rem-operators-post postfixes ops qd)
  (define start-tok (peek))
  (let loop ([e0 (parse-w-rem-operators (cdr ops) qd)])
    (define tokstr (token->str (peek)))
    (if (set-member? postfixes tokstr)
        (let ([op-tok (peek)])
          (advance)
          (loop (emit-expr `(,(emit-expr `(ref ,(string->symbol tokstr)) op-tok) ,e0) start-tok)))
        e0)))
(define (parse-w-rem-operators ops qd)
  (if (null? ops)
      (parse-small qd)
      (match (car (first ops))
        ['bin (parse-w-rem-operators-bin (list->set (cdr (first ops))) ops qd)]
        ['pre (parse-w-rem-operators-pre (list->set (cdr (first ops))) ops qd)]
        ['post (parse-w-rem-operators-post (list->set (cdr (first ops))) ops qd)])))

(define (parse-w-rem-operators-bin group ops qd)
  (define start-tok (peek))
  
  ;; 1. Parse the Left-Hand Side using the *next* higher precedence level
  (let loop ([lhs (parse-w-rem-operators (rest ops) qd)])
    
    (define op-tok (peek))
    (define tokstr (token->str op-tok))
    
    ;; 2. Loop while the next token is part of the current operator group
    (if (and (not (eq? 'ref (token->tag op-tok))) 
             (set-member? group tokstr))
        (begin 
          (advance)
          (let* ([tokstrsym (string->symbol tokstr)]
                 [op-ref (emit-expr `(ref ,tokstrsym) op-tok)]
                 ;; 3. Parse the Right-Hand Side using the *next* higher precedence level
                 ;; (Do NOT recurse with 'ops', or you get right-associativity)
                 [rhs (parse-w-rem-operators (rest ops) qd)])
            
            ;; 4. Wrap the result: (op lhs rhs)
            ;; 'start-tok' preserves the position of the far-left element.
            ;; 'emit-expr' automatically uses 'last-consumed-tok' (from rhs) for the end pos.
            (loop (emit-expr `(,op-ref ,lhs ,rhs) start-tok))))
        
        ;; 5. If no operator matches, return the accumulated result
        lhs)))
#;
(define (parse-w-rem-operators-bin group ops qd)
  (define start-tok (peek))
  (define e0 (parse-w-rem-operators (rest ops) qd))
  (define op-tok (peek))
  (define tokstr (token->str op-tok))
  (define tokstrsym (string->symbol tokstr))
  
  (if (and (not (eq? 'ref (token->tag op-tok))) (set-member? group tokstr))
      (begin (advance)
             (let ([op-ref (emit-expr `(ref ,tokstrsym) op-tok)]
                   [e1 (parse-w-rem-operators ops qd)])
               (match e1
                 [`(syn ,_ (syn ,_ ref ,(? (lambda (x) (equal? x tokstrsym)))) ,e+s ...)
                  (emit-expr `(,op-ref ,e0 ,@e+s) start-tok)]
                 [_ (emit-expr `(,op-ref ,e0 ,e1) start-tok)])))
      e0))

(define (parse qd)
  ; parses a single expression from toks, checking operators, then postfixes, prefixes, atoms
  ; (which include keywords)
  (parse-w-rem-operators operators qd))

(define (parse-N parser n qd)
  (match n
    [0 '()]
    [_ (cons (parser qd) (parse-N parser (sub1 n) qd))]))

(define (make-parse-id-then-N-emit parser N qd)
  (lambda ()
    (define start-tok (peek))
    (emit-expr (parse-id-then-N parser N qd) start-tok)))

(define (parse-id-then-N parser N qd)
  (define tag (string->symbol (token->str (peek))))
  (advance)
  (define es (parse-N parser N qd))
  `(,tag ,@es))

(define (parse-def is-toplevel qd)
  (define start-tok (peek))
  (advance) ;; consume 'def'

  (define pattern-e (parse qd))

  (when (equal? (token->str (peek)) "=>")
    (advance))

  (define w-eq-b (parse qd))

  (let loop ([w-eq-b w-eq-b] [guard-e #f])
    (match (last w-eq-b)
      ['when
	  (define guard (parse qd))
	(define eq-b (parse qd))
	(loop eq-b guard)]
      [_
       (define rest-e (if is-toplevel (parse-top-level) (parse qd)))
       (emit-expr `(,(string->symbol (token->str start-tok))
		    ,pattern-e
                    ,@(if guard-e `(,guard-e) `())
                    ,w-eq-b ,rest-e)
                  start-tok)])))

(define (parse-let is-toplevel qd)
  (define start-tok (peek))
  (advance)
  (define pat (parse-small qd))
  (when (equal? (token->str (peek)) "=") (advance))
  (define rhs (parse qd))
  (when (equal? (token->str (peek)) "in") (advance))
  (define body (if is-toplevel (parse-top-level) (parse qd)))
  (emit-expr `(let ,pat ,rhs ,body) start-tok))

(define (parse-top-level)
      (define start-tok (peek))
      (define str (token->str start-tok))
      
      (match str
        [""
         (emit-expr '(top-level) start-tok)]
	
        ["def" (parse-def #t 0)]
	
        ["blessed"
         (define tag-str (parse-id-then-N parse 2 0))
         (define body (parse-top-level))
         (emit-expr `(,@tag-str ,body) start-tok)]

	["let" (parse-let #t 0)]
        [(or "use" "include" "bless")
         (define tag-str (parse-id-then-N parse 1 0))
         (define body (parse-top-level))
         (emit-expr `(,@tag-str ,body) start-tok)]
        
        [_ 
         (define e (parse 0)) ;; Parse the standalone expression
         (define rest (parse-top-level)) ;; Recurse to parse the rest of the file
         ;; Wrap them in a sequence/begin block so the AST stays a single tree
         (emit-expr `(begin ,e ,rest) start-tok)]))


;; Defines infix operators, precedence, grouping, associativity
(define operators
  `((bin ";")
    (bin "<-")
    (pre "->")
    (bin "&" "|")
    (bin "<" "<=" ">" ">=" "=" "/=")
    (bin ":=")
    (bin "+" "-")
    (bin "*" "/" "%")
    (bin "^")
    (post "...")
    (bin ":")
    (bin "?")
    (bin ".")
    (pre "!")))


;; Defines keyword parsers
(define keywords
  (hash "def"    (lambda (qd) (lambda () (parse-def #f qd)))
	"pure"    (lambda (qd) (lambda () (parse-def #f qd)))
        "let"    (lambda (qd) (lambda () (parse-let #f qd)))
        "use"    (lambda (qd) (make-parse-id-then-N-emit parse 2 qd))
        "if"     (lambda (qd) (make-parse-id-then-N-emit parse 3 qd))
        "lambda" (lambda (qd) (make-parse-id-then-N-emit parse 2 qd))
	"return" (lambda (qd) (make-parse-id-then-N-emit parse 1 qd))
	"do" (lambda (qd) (make-parse-id-then-N-emit parse 1 qd))
	"bless" (lambda (qd) (make-parse-id-then-N-emit parse 1 qd))
        "#"      (lambda (qd) (make-parse-id-then-N-emit parse 2 qd))
        "new"    (lambda (qd) (make-parse-id-then-N-emit parse 3 qd))
        "renew"  (lambda (qd) (make-parse-id-then-N-emit parse 2 qd))))


(define (parse-port filename input-port)
  (define lex (make-tinkr-lexer filename input-port))
  
  (set! current-toks '())
  (set! last-consumed-tok #f)
  (set! current-lex lex)
  
  (define file-ast (parse-top-level))
  
  (if (eq? 'eof (token->tag (peek)))
      `(module ,filename () ,file-ast) ;; Note: No raw-toks list available anymore
      (error (format "End of file expected, instead: '~a'\nat ~a:~a"
	       (token->str (peek)) (pos->file (token->pos (peek))) (pos->startline (token->pos (peek)))))))

;; Parses a module from a filename
(define (parse-file filename)
  (with-input-from-file (normalize-path filename)
    (lambda () (parse-port filename (current-input-port)))))



