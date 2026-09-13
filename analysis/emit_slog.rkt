#lang racket

(require "../rkt/parser.rkt")

(define (unique_name name)
  (symbol->string (gensym (~a name "_"))))

(struct located_term (prov term))

(define (src_facts term)
  (match term
    [(located_term `(src . ,location) term) `(,@(src_facts term) (src ,term ,@location))]
    [(? list?) (append-map src_facts term)]
    [(or (? string?) (? exact-integer?) (? symbol?)) '()]))

(define (term_text term)
  (match term
    [(located_term _ term) (term_text term)]
    [(? string?) (~s term)]
    [(? exact-integer?) (~a term)]
    [`(,(? symbol? tag) ,fields ...)
     (~a "(" (string-join (cons (~a tag) (map term_text fields)) " ") ")")]
    [(? list?) (~a "[" (string-join (map term_text term) " ") "]")]))

(define (notmodeled_term what)
  `(notmodeled ,(format "~a" what)))

(define (free_name_term name)
  (match name
    ['true '(true_lit)]
    ['false '(false_lit)]
    ['= '(eq_prim)]
    [(or '+ '- '* '/) `(num_prim ,(symbol->string name))]
    [(or '< '<= '> '>=) `(cmp_prim ,(symbol->string name))]
    [_ `(free_var ,(symbol->string name))]))

(define (expr_term expr scope_env)
  (match expr
    [`(syn ,_ begin ,last_expr ,(app strip-prov `(top-level))) (expr_term last_expr scope_env)]
    [`(syn ,prov . ,form) (located_term prov (form_term form scope_env))]))

(define (form_term form scope_env)
  (define (inner sub_expr)
    (expr_term sub_expr scope_env))
  (match form
    [`(const ,value)
     (match value
       [(? exact-integer?) `(num_lit ,value)]
       [(? string?) `(str_lit ,value)]
       [_ (notmodeled_term value)])]
    [`(ref ,name)
     (match (assq name scope_env)
       [#f (free_name_term name)]
       [`(,_ . ,unique) `(bound_var ,unique)])]
    [`(lambda ,(app strip-prov `((ref ,names) ...)) ,body)
     (define unique_names (map unique_name names))
     `(lam ,unique_names ,(expr_term body (append (map cons names unique_names) scope_env)))]
    [`(let ,(app strip-prov `(ref ,name))
        ,bound_expr
        ,body)
     (define unique (unique_name name))
     `(let ,unique
        ,(inner bound_expr)
        ,(expr_term body (cons (cons name unique) scope_env)))]
    [`(def ,(app strip-prov `((ref ,name) (ref ,params) ...)) ,body ,rest_expr)
     (define unique (unique_name name))
     (define unique_params (map unique_name params))
     (define body_env (append (map cons params unique_params) (cons (cons name unique) scope_env)))
     `(def ,unique
           ,unique_params
           ,(expr_term body body_env)
           ,(expr_term rest_expr (cons (cons name unique) scope_env)))]
    [`(if ,cnd ,thn ,elz)
     `(if ,(inner cnd)
          ,(inner thn)
          ,(inner elz))]
    [`(begin
        ,first_expr
        ,rest_expr)
     `(begin
        ,(inner first_expr)
        ,(inner rest_expr))]
    [`(,(? symbol? tag) . ,_) (notmodeled_term tag)]
    [`(,operator ,operands ...) `(app ,(inner operator) ,(map inner operands))]
    [_ (notmodeled_term form)]))

(module+ main
  (define program_path (command-line #:args (path) path))
  (match-define `(module ,_ ,_
                   ,module_ast)
    (parse-file program_path))
  (define program_term (expr_term module_ast '()))
  (display (format "include \"1mcfa.slog\"\n\nrule\n(program\n ~a)\n\n" (term_text program_term)))
  (for-each displayln
            (map (lambda (fact) (format "rule ~a" (term_text fact))) (src_facts program_term))))
