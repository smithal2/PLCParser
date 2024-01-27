#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp y2 advanced-letrec reset-global-env)

(define (y2 which f1 f2) "nyi")
(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body) ...) letrec-body)
     #'(error "nyi")]))

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define (symImproperList? lst)
  (and (pair? lst) (let recur ([lst lst])
                     (if (symbol? lst) #t
                         (if (symbol? (car lst))
                             (recur (cdr lst))
                             #f)))))

(define (letBasicAssignment? lst)
  (if (null? lst) #t
      (if (and (list? lst)
               (= (length (car lst)) 2)
               (symbol? (caar lst))
               (expression? (parse-exp (cadar lst))))
          (letBasicAssignment? (cdr lst))
          #f)))

(define (letBasicAssignmentType? lst)
  (if (null? lst) #t
      (if (and (list? lst)
               (= (length (car lst)) 2)
               (var-exp? (caar lst))
               (expression? (cadar lst)))
          (letBasicAssignmentType? (cdr lst))
          #f)))

(define (lit-exp? data)
  (lambda (x)
    (ormap 
     (lambda (pred) (pred x))
     (list number? vector? boolean? symbol? string? pair? null?))))

(define (var-exp? x)
  (cases expression x
    [var-exp (id) #t]
    [else #f]))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data lit-exp?)]
  [lambda-exp
   (id (list-of? symbol?))
   (body (list-of? expression?))]
  [lambda-rest-exp
   (id symbol?)
   (body (list-of? expression?))]
  [lambda-improper-exp
   (id symImproperList?)
   (body (list-of? expression?))]
  [letstar-exp 
   (assignment letBasicAssignmentType?)
   (bodies (list-of? expression?))]
  [letrec-exp 
   (proc-names (list-of? symbol?))
   (idss (list-of? (list-of? symbol?)))
   (bodiess (list-of? (list-of? expression?)))
   (letrec-bodies (list-of? expression?))]
  [let-exp 
   (assignment letBasicAssignmentType?)
   (bodies (list-of? expression?))]
  [if-exp
   (condition expression?)
   (true expression?)
   (false expression?)]
  [set-exp
   (id var-exp?)
   (value expression?)]
  [app-exp
   (rator expression?)
   (rand (list-of? expression?))]
  [and-exp
   (expressions (list-of? expression?))]
  [or-exp
   (expressions (list-of? expression?))]
  [begin-exp
    (expressions (list-of? expression?))]
  [while-exp
   (condition expression?)
   (expressions (list-of? expression?))]
  [cond-exp
   (expression (list-of? expression?))]
  [define-exp
    (name symbol?)
    (content (list-of? expression?))]
)

;; environment type definitions

(define (scheme-value? x) #t)
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)]
  [recursively-extended-env-record
   (proc-names (list-of? symbol?))
   (idss (list-of? (list-of? symbol?)))
   (bodiess (list-of? (list-of? expression?)))
   (old-env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (parameters (lambda (param) (or ((list-of? symbol?) param) (symbol? param) (and (pair? param) (not (list? param))))))
   (bodies (list-of? expression?))
   (env environment?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

; Again, you'll probably want to use your code from A11b

(define (parse-exp datum)
  (cond
    [(symbol? datum) (var-exp datum)]
    [(number? datum) (lit-exp datum)]
    [(boolean? datum) (lit-exp datum)]
    [(string? datum) (lit-exp datum)]
    [(list? datum)
     (if (and (equal? (1st datum) 'quote) (= (length datum) 2)) (lit-exp (2nd datum))
         (case (car datum)
           [(lambda) (if (>= (length datum) 3) (cond
                                                 [((list-of? symbol?) (2nd datum)) (lambda-exp (2nd datum) (map parse-exp (cddr datum)))]
                                                 [(symbol? (2nd datum)) (lambda-rest-exp (2nd datum) (map parse-exp (cddr datum)))]
                                                 [(pair? (2nd datum)) (lambda-improper-exp (2nd datum) (map parse-exp (cddr datum)))]
                                                 [else (error 'parse-exp "improper format for arguments: ~s" datum)])
                         (error 'parse-exp "not enough bodies in lambda exp: ~s" datum))]
           [(let let*) (if (letBasicAssignment? (2nd datum)) ((case (1st datum) ((let) let-exp) ((let*) letstar-exp)) (map (lambda (x) (list (parse-exp (car x)) (parse-exp (cadr x)))) (2nd datum)) (map parse-exp (cddr datum))) (letrec-exp (list (2nd datum)) (list (map car (3rd datum))) (list (map parse-exp (cdddr datum))) (list (app-exp (var-exp (2nd datum)) (map (lambda (item) (parse-exp (cadr item))) (3rd datum))))))]
           [(letrec) (if (letBasicAssignment? (2nd datum)) (letrec-exp
                                                            (map car (2nd datum))
                                                            (map cadadr (2nd datum))
                                                            (map (lambda (bodies) (map parse-exp (cddadr bodies))) (2nd datum))
                                                            (map parse-exp (cddr datum)))
                         (error 'parse-exp "variable assignment is wrong: ~s" datum))]
           [(if) (if (and (lit-exp? (2nd datum)) (= (length datum) 3)) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (app-exp (var-exp 'void) '())) (if (and (= (length datum) 4) (lit-exp? (2nd datum))) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum))) (error 'parse-exp "wrong if statement format: ~s" datum)))]
           [(and) (and-exp (map parse-exp (cdr datum)))]
           [(define) (if (symbol? (2nd datum)) (define-exp (2nd datum) (map parse-exp (cddr datum))) (error 'parse-exp "define needs a symbol as a name: ~s" datum))]
           [(or) (or-exp (map parse-exp (cdr datum)))]
           [(begin) (begin-exp (map parse-exp (cdr datum)))]
           [(while) (if (< 2 (length datum)) (while-exp (parse-exp (cadr datum)) (map parse-exp (cdr (cdr datum)))) (error 'parse-exp "need condition and body: ~s" datum))]
           [(cond) (cond-exp (map parse-exp (cdr datum)))]
           [(set!) (if (and (= (length datum) 3) (symbol? (2nd datum))) (set-exp (var-exp (2nd datum)) (parse-exp (3rd datum))) (error 'parse-exp "wrong set! statement format: ~s" datum))]
           [else (app-exp (parse-exp (1st datum)) (map (lambda (y) (parse-exp y)) (cdr datum)))]))]
    [else (error 'parse-exp "bad expression: ~s" datum)]))

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+

; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define (empty-env) (empty-env-record))

(define global-env #())
(define global-env-refs '())

(define reset-global-env
  (lambda ()
    (set! global-env #())))

(define (extend-env syms vals env)
  (extended-env-record syms vals env))

(define (extend-env-recursively proc-names idss bodiess old-env)
  (recursively-extended-env-record proc-names idss bodiess old-env))

(define (list-find-position sym los)
  (let loop ([los los] [pos 0])
    (cond [(null? los) #f]
          [(eq? sym (car los)) pos]
          [else (loop (cdr los) (add1 pos))])))

(define-datatype cell cell?
  [init-cell
   (val (list-of? expression?))]
  [cell-ref
   (cel cell?)]
  [cell-set!
   (cel cell?)
   (val (list-of? expression?))])

(define (cell-funct cel)
  (cases cell cel
    [init-cell (val)
     (box val)]
    [cell-ref (cel)
     (unbox cel)]
    [cell-set! (cel val)
     (set-box! cel val)]
    [cell? (box? cel)]))

(define-datatype reference reference?
  [init-reference
   (index number?)
   (name symbol?)]
  [deref
   (ref reference?)]
  [set-ref!
   (ref reference?)
   (val expression?)])
           
         
	    
(define (apply-env env sym)
  (cases environment env
    [empty-env-record ()
                      (error 'env "variable ~s not found." sym)]
    [extended-env-record (syms vals env)
                         (let ((pos (list-find-position sym syms)))
                           (if (number? pos)
                               (list-ref vals pos)
                               (apply-env env sym)))]
    [recursively-extended-env-record (proc-names idss bodiess old-env)
                                   (let ([pos (list-find-position sym proc-names)])
                                     (if (number? pos)
                                         (closure (list-ref idss pos)
                                                  (list-ref bodiess pos)
                                                  env)
                                         (apply-env old-env sym)))]))

(define (reset-global-env) "nyi")

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
    (lambda (exp)
        (cases expression exp
          [var-exp (symbol) exp] ;; do nothing
          [lit-exp (literal) exp] ;; do nothing
          [lambda-exp (id bodies) (lambda-exp id (map syntax-expand bodies))]
          [letrec-exp (proc-names idss bodiess letrec-bodies) (letrec-exp proc-names idss (map (lambda (bodies) (map syntax-expand bodies)) bodiess) (map syntax-expand letrec-bodies))]
          [let-exp (assignment bodies) (let-exp (map (lambda (x) (cons (1st x) (list (syntax-expand (2nd x))))) assignment) (map syntax-expand bodies))]
          [if-exp (condition true false) (if-exp (syntax-expand condition) (syntax-expand true) (syntax-expand false))]
          [set-exp (id value) (set-exp id (syntax-expand value))]
          [app-exp (rator rand) (app-exp rator (map syntax-expand rand))]
          [and-exp (exps)
                   (cond [(null? exps) (lit-exp #t)]
                         [(null? (cdr exps)) (syntax-expand (car exps))]
                         [else (if-exp (syntax-expand (car exps))
                                       (syntax-expand (and-exp (cdr exps)))
                                       (lit-exp #f))])]
          [or-exp (exps)
                  (cond
                    [(null? exps) (lit-exp #f)]
                    [(null? (cdr exps)) (syntax-expand (car exps))]
                    [else (if-exp (syntax-expand (car exps)) (syntax-expand (car exps)) (syntax-expand (or-exp (cdr exps))))])]
          [letstar-exp (assignment bodies) (if (null? (cdr assignment)) (syntax-expand (let-exp assignment bodies))
                                               (syntax-expand (let-exp (list(car assignment)) (list (syntax-expand (letstar-exp (cdr assignment) bodies)))))) ]
          [cond-exp (exps) (if (null? exps) (app-exp (var-exp 'void) '())
                               (if (and (equal? 'else (2nd (2nd (car exps)))) (null? (cdr exps))) (syntax-expand (car (3rd (car exps))))
                                   (if-exp (syntax-expand (2nd (car exps))) (syntax-expand (car (3rd (car exps)))) (syntax-expand (cond-exp (cdr exps))))))]
          [begin-exp (exps) (app-exp (lambda-exp '() (map syntax-expand exps)) '())]
          [lambda-rest-exp (id bodies) (lambda-rest-exp id (map syntax-expand bodies))]
          [lambda-improper-exp (id bodies) (lambda-improper-exp id (map syntax-expand bodies))]
          [while-exp (condition expressions) (while-exp (syntax-expand condition) (map syntax-expand expressions))]
          [define-exp (name expressions) (define-exp name (map syntax-expand expressions))])))

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define (top-level-eval form)
    ; later we may add things that are not expressions.
  (eval-exp form init-env))

; eval-exp is the main component of the interpreter

(define (eval-exp exp env)
  (cases expression exp
    [lit-exp (datum) datum]
    [var-exp (id) (apply-env env id)]
    [if-exp (condition true false)
            (if (eval-exp condition env) (eval-exp true env) (eval-exp false env))]
    [app-exp (rator rands)
             (let ([proc-value (eval-exp rator env)]
                   [args (map (lambda (rands) (eval-exp rands env)) rands)])
                   (apply-proc proc-value args))]
    [let-exp (assignment bodies)
             (let recur ([assignment assignment]
                         [syms null]
                         [vals null])
               (if (null? assignment)
                   (car (reverse (map (lambda (body) (eval-exp body (extendeded-env-record-record syms vals env))) bodies)))
                   (recur (cdr assignment)
                     (cons (cadaar assignment) syms)
                     (cons (eval-exp (cadar assignment) env) vals))))]
    [letrec-exp (proc-names idss bodiess letrec-bodies)
                (car (reverse (map (lambda (letrec-body)
                                     (eval-exp letrec-body (recursively-extended-env-record proc-names idss bodiess env))) letrec-bodies)))]
    [lambda-exp (id bodies) ; (lambda (x y) ...)
                (closure id bodies env)]
    [lambda-rest-exp (id bodies) ; (lambda x ...)
                     (closure id bodies env)]
    [lambda-improper-exp (id bodies) ; (lambda (x . y) ...)
                         (closure id bodies env)]
    [define-exp (name expressions)
      (begin 
        (set! global-env (list->vector (append (vector->list global-env) (init-cell expressions))))
        (set! global-env-refs (append global-env-refs (list (init-reference (- (vector-length global-env) 1) name))))
        (display "\nGloval Env Vlaues: \n")
        (display global-env)
        (display "\nGloval Env REfs: \n")
        (display global-env-refs)
      )]
    [else (error 'eval-exp "Bad abstract syntax: ~a" exp)]))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define (apply-proc proc-value args)
  (cases proc-val proc-value
    [prim-proc (name) (apply-prim-proc name args)]
    [closure (param bodies env)
             (car (reverse (map (lambda (body)
                                  (eval-exp body (if (symbol? param) (extended-env-record (list param) (list args) env)
                                                     (if ((list-of? symbol?) param) (extended-env-record param args env)
                                                         (extended-env-record (flatten param) (append (take args (sub1 (length (flatten param)))) (list (drop args (sub1 (length (flatten param)))))) env))))) bodies)))]
    [else (error 'apply-proc
                 "Attempt to apply bad procedure: ~s" 
                 proc-value)]))

(define (our-map proc items)
  (if (null? items) null
      (cons (apply-proc proc (list (car items))) (our-map proc (cdr items)))))


#|(define *prim-proc-names* '(+ - * / add1 sub1 cons = not zero?))|#
(define *prim-proc-names* '(cons append void apply map assq eq? eqv? equal? vector-ref quotient list-tail vector-set! + - * / = < > <= >= list vector add1 sub1 zero? not car cdr caar cadr cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr null? length list->vector list? pair? procedure? vector->list vector? number? symbol?))

(define init-env         ; for now, our initial global environment only contains 
  (extended-env-record   ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc
        *prim-proc-names*)
   (empty-env-record)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define (apply-prim-proc prim-proc args)
  (case prim-proc
    [(+ - * / = < > <= >= list vector void)
     (case prim-proc
       [(+) (apply + args)]
       [(-) (apply - args)]
       [(*) (apply * args)]
       [(/) (apply / args)]
       [(=) (apply = args)]
       [(<) (apply < args)]
       [(>) (apply > args)]
       [(<=) (apply <= args)]
       [(>=) (apply >= args)]
       [(list) (apply list args)]
       [(vector) (apply vector args)])]
       [(void) (void)]
    [(add1 sub1 zero? not car cdr caar cadr cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr null? length list->vector list? pair? procedure? vector->list vector? number? symbol?)
     (if (= (length args) 1)
         (case prim-proc
           [(add1) (+ (1st args) 1)]
           [(sub1) (- (1st args) 1)]
           [(zero?) (zero? (1st args))]
           [(not) (not (1st args))]
           [(car) (car (1st args))]
           [(cdr) (cdr (1st args))]
           [(caar) (caar (1st args))]
           [(cadr) (cadr (1st args))]
           [(cdar) (cdar (1st args))]
           [(cddr) (cddr (1st args))]
           [(caaar) (caaar (1st args))]
           [(caadr) (caadr (1st args))]
           [(cadar) (cadar (1st args))]
           [(cdaar) (cdaar (1st args))]
           [(caddr) (caddr (1st args))]
           [(cdadr) (cdadr (1st args))]
           [(cddar) (cddar (1st args))]
           [(cdddr) (cdddr (1st args))]
           [(null?) (null? (1st args))]
           [(length) (length (1st args))]
           [(list->vector) (list->vector (1st args))]
           [(list?) (list? (1st args))]
           [(pair?) (pair? (1st args))]
           [(procedure?) (proc-val? (1st args))]
           [(vector->list) (vector->list (1st args))]
           [(vector?) (vector? (1st args))]
           [(number?) (number? (1st args))]
           [(symbol?) (symbol? (1st args))])
         (error 'apply-prim-proc "Exception in ~s: Expected 1 argument but got ~s." prim-proc (length args)))]
    [(cons assq eq? eqv? equal? vector-ref map apply append quotient list-tail)
     (if (= (length args) 2)
         (case prim-proc
           [(cons) (cons (1st args) (2nd args))]
           [(apply) (apply-proc (1st args) (2nd args))]
           [(map) (our-map (1st args) (2nd args))]
           [(assq) (assq (1st args) (2nd args))]
           [(eq?) (eq? (1st args) (2nd args))]
           [(eqv?) (eqv? (1st args) (2nd args))]
           [(equal?) (equal? (1st args) (2nd args))]
           [(vector-ref) (vector-ref (1st args) (2nd args))]
           [(append) (append (1st args) (2nd args))]
           [(quotient) (quotient (1st args) (2nd args))]
           [(list-tail) (list-tail (1st args) (2nd args))])
         (error 'apply-prim-proc "Exception in ~s: Expected 2 arguments but got ~s." prim-proc (length args)))]
    [(vector-set!) (if (= (length args) 3) (vector-set! (1st args) (2nd args) (3rd args)) (error 'apply-prim-proc "Exception in ~s: Expected 3 arguments but got ~s." prim-proc (length args)))]
    [else (error 'apply-prim-proc 
                 "Bad primitive procedure name: ~s" 
                 prim-proc)])) ; missing atom?, make-vector, display, newline

(define (rep)      ; "read-eval-print" loop.
  (display "--> ")
  ;; notice that we don't save changes to the environment...
  (let ([answer (top-level-eval (parse-exp (read)))])
    ;; TODO: are there answers that should display differently?
    (pretty-print answer) (newline)
    (rep)))  ; tail-recursive, so stack doesn't grow.

(define (eval-one-exp x)
  (top-level-eval (syntax-expand (parse-exp x))))