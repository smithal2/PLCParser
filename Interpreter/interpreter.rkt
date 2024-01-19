#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)

(provide add-macro-interpreter)
(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
(lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define symList?
  (lambda (lst)
    (if (null? lst) #t
        (if (symbol? (car lst)) (symList? (cdr lst))
            #f))))

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
   (id symList?)
   (body (list-of? expression?))]
  [unlimited-lambda-exp
   (id symList?)
   (body (list-of? expression?))]
  [no-body-lambda-exp
   (id symList?)]
  [let-exp-wo-body
   (assignment letBasicAssignmentType?)]
  [letstar-exp 
   (assignment letBasicAssignmentType?)
   (bodies (list-of? expression?))]
  [letrec-exp 
   (assignment letBasicAssignmentType?)
   (bodies (list-of? expression?))]
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
)

;; environment type definitions

(define (scheme-value? x) #t)
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (parameters (list-of? symbol?))
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

(define (hasList? lst)
  (if (null? lst) #f
      (if (list? (car lst)) #t (hasList? (cdr lst)))))

(define (unlimited-arg-lambda lst datum)
  (if (and (= (length lst) 1) (symbol? (car lst))) (no-body-lambda-exp lst)
      (if (and (= (length lst) 1) (not (symbol? (car lst)))) (error 'parse-exp "The argument isn't a symbol: ~s" datum)
          (let ([everything-but-last (reverse (cdr (reverse lst)))] [last-element (cadr (reverse lst))])
            (if (and (hasList? lst) (symList? everything-but-last)) (unlimited-lambda-exp everything-but-last last-element)
                (if (and (not (hasList? lst)) (symList? lst)) (no-body-lambda-exp lst)
                    (error 'parse-exp "An argument isn't a symbol: ~s" datum)))))))

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
           [(lambda) (if (>= (length datum) 3) (if (list? (2nd datum)) (if (symList? (2nd datum)) (lambda-exp (2nd datum) (map parse-exp (cddr datum))) (error 'parse-exp "list of variables must consist of symbols: ~s" datum))
                                                   (unlimited-arg-lambda (cdr datum) datum)) (error 'parse-exp "not enough bodies in lambda exp: ~s" datum))]
           [(let let* letrec) (if (letBasicAssignment? (2nd datum)) (if (= 2 (length datum)) (let-exp-wo-body (2nd datum)) (let-exp (map (lambda (x) (list (parse-exp (car x)) (parse-exp (cadr x)))) (2nd datum)) (map parse-exp (cddr datum)))) (error 'parse-exp "variable assignment is wrong: ~s" datum))]
           [(if) (if (and (lit-exp? (2nd datum)) (= (length datum) 3)) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (app-exp (var-exp 'void) '())) (if (and (= (length datum) 4) (lit-exp? (2nd datum))) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum))) (error 'parse-exp "wrong if statement format: ~s" datum)))]
           [(set!) (if (and (= (length datum) 3) (symbol? (2nd datum))) (set-exp (var-exp (2nd datum)) (parse-exp (3rd datum))) (error 'parse-exp "wrong set! statement format: ~s" datum))]
           [else (if (> (length datum) 1) (app-exp (parse-exp (1st datum)) (map (lambda (y) (parse-exp y)) (cdr datum))) (error 'parse-exp "Application Expression with no args: ~s" datum))]))]
    [else (error 'parse-exp "bad expression: ~s" datum)]))

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+




; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define (empty-env) (empty-env-record))

(define (extend-env syms vals env)
  (extended-env-record syms vals env))

(define (list-find-position sym los)
  (let loop ([los los] [pos 0])
    (cond [(null? los) #f]
          [(eq? sym (car los)) pos]
          [else (loop (cdr los) (add1 pos))])))
	    
(define (apply-env env sym)
  (cases environment env
    [empty-env-record ()
                      (error 'env "variable ~s not found." sym)]
    [extended-env-record (syms vals env)
                         (let ((pos (list-find-position sym syms)))
                           (if (number? pos)
                               (list-ref vals pos)
                               (apply-env env sym)))]))


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

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
                   (car (reverse (map (lambda (body) (eval-exp body (extend-env syms vals env))) bodies)))
                   (recur (cdr assignment)
                     (cons (cadaar assignment) syms)
                     (cons (eval-exp (cadar assignment) env) vals))))]
    [lambda-exp (id bodies)
                (closure id bodies env)]
    [else (error 'eval-exp "Bad abstract syntax: ~a" exp)]))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define (apply-proc proc-value args)
  (cases proc-val proc-value
    [prim-proc (name) (apply-prim-proc name args)]
    [closure (parameters bodies env) (car (reverse (map (lambda (body) (eval-exp body (extend-env parameters args env))) bodies)))]
    [else (error 'apply-proc
                 "Attempt to apply bad procedure: ~s" 
                 proc-value)]))


#|(define *prim-proc-names* '(+ - * / add1 sub1 cons = not zero?))|#
(define *prim-proc-names* '(cons assq eq? equal? vector-ref vector-set! + - * / = < > <= >= list vector add1 sub1 zero? not car cdr caar cadr cdar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr null? length list->vector list? pair? procedure? vector->list vector? number? symbol?))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define (apply-prim-proc prim-proc args)
  (case prim-proc
    [(+ - * / = < > <= >= list vector)
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
           [(procedure?) (or (if (and (list? (1st args)) (member (car (1st args)) '(prim-proc closure))) #t #f) (procedure? (1st args)))]
           [(vector->list) (vector->list (1st args))]
           [(vector?) (vector? (1st args))]
           [(number?) (number? (1st args))]
           [(symbol?) (symbol? (1st args))])
         (error 'apply-prim-proc "Exception in ~s: Expected 1 argument but got ~s." prim-proc (length args)))]
    [(cons assq eq? equal? vector-ref)
     (if (= (length args) 2)
         (case prim-proc
           [(cons) (cons (1st args) (2nd args))]
           [(assq) (assq (1st args) (2nd args))]
           [(eq?) (eq? (1st args) (2nd args))]
           [(equal?) (equal? (1st args) (2nd args))]
           [(vector-ref) (vector-ref (1st args) (2nd args))])
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
  (top-level-eval (parse-exp x)))
