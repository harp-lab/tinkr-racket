#lang racket

(provide make-tinkr-lexer
         make-token
         synth-token
         token->tag
         token->pos
         token->str
         pos->file
         pos->startline
         pos->startcol
         pos->endline
         pos->endcol)

(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(define token->tag second)
(define token->pos third)
(define token->str fourth)
(define pos->file second)
(define pos->startline third)
(define pos->startcol fourth)
(define pos->endline fifth)
(define pos->endcol sixth)

(define (make-token tag filename line-pos col-pos lexeme)
  `(token ,tag
          (pos ,filename ,line-pos ,col-pos ,line-pos ,(+ col-pos (string-length lexeme)))
          ,lexeme))

(define synth-token (make-token 'synthetic "<internal>" 0 0 ""))

(define make-tinkr-lexer
      (lambda (filename input-port)
        (define line-pos 0)
        (define col-pos 0)

        (define current-lex-proc #f)
        
        (define (advance-line!)
          (set! col-pos 0)
          (set! line-pos (+ 1 line-pos)))
        
        (define (advance-col! [x 1])
          (set! col-pos (+ x col-pos)))
        
        (define (emit-token tag lexeme)
          (begin0 (make-token tag filename line-pos col-pos lexeme)
            (advance-col! (string-length lexeme))))
	
	;; normal tinkr lexing
        (define lex-standard
          (lexer 
           [(eof) (emit-token 'eof "")]
           
           [(:: ";;" (:* (:& (:~ "\n") any-char))) (emit-token 'comment lexeme)]
           [(:: "'" (:* (:or "\\'" (:& (:~ (:or "\n" "'")) any-char))) "'")
            (emit-token 'ref (substring lexeme 1 (- (string-length lexeme) 1)))]
           ["|" (emit-token 'op lexeme)]
           ["(" (emit-token 'popen lexeme)]
           [")" (emit-token 'pclose lexeme)]
           ["[" (emit-token 'sopen lexeme)]
           ["]" (emit-token 'sclose lexeme)]
           ["{" (emit-token 'copen lexeme)]
           ["}" (emit-token 'cclose lexeme)]
           ["`" (emit-token 'quote lexeme)]
           ["~" (emit-token 'not lexeme)]
           ["," (emit-token 'unquote lexeme)]
           ["λ" (emit-token 'id "lambda")]
           ["\r" (emit-token 'space lexeme)]
           [#\newline
            (begin0 (emit-token 'newline lexeme)
		    (advance-line!))]
           [(:+ (:or #\tab #\space)) (emit-token 'space lexeme)]
           [(:: "\"" (:* (:or (:: "\\" any-char) (char-complement (:or "\"")))) "\"")
            (emit-token 'str (string-append "\"" (with-input-from-string lexeme read) "\""))]
           [(:+ (:/ "0" "9")) (emit-token 'num lexeme)]
           [(:: (:or (:/ "A" "Z") (:/ "a" "z") (:/ "0" "9") "_")
                (:* (:or (:/ "A" "Z") (:/ "a" "z") (:/ "0" "9") "_" "'")))
            (emit-token 'id lexeme)]
           ["\\" (emit-token 'op lexeme)]
           [(:+ (:& (:or "." (:/ "!" "~"))
                    (:~ (:or (:/ "A" "Z")
                             (:/ "a" "z")
                             (:/ "0" "9")
                             "_"
                             "\""
                             "~"
                             ","
                             "`"
                             "'"
                             "\\"
                             "("
                             ")"
                             "["
                             "]"
                             "{"
                             "}"
                             "|"))))
            (emit-token 'op lexeme)]))
        
        (set! current-lex-proc lex-standard)

	;; emit the generator
        (lambda ()
	  (let loop ([tok (current-lex-proc input-port)])
	    (match tok
	      [`(token ,(or 'space 'newline 'comment) ,_ ...)
	       (loop (current-lex-proc input-port))]
	      [_ tok])))))


