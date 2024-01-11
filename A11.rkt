#lang racket

(require "../chez-init.rkt")
(provide bintree-to-list bintree-add leaf-node interior-node parse-exp unparse-exp)


(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left-tree bintree?)
   (right-tree bintree?)))

; I've provide this one as a sample to you.
; It's used by the testcases though  so don't mess with it.
(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      [interior-node (value left right)
                (list value
                      (bintree-to-list left)
                      (bintree-to-list right))]
      [leaf-node (datum)
                 datum])))
                
; Here's the one you need to solve
(define (bintree-add bt num)
  (if (equal? (car bt) 'leaf-node)
      (leaf-node (+ (cadr bt) num))
      (interior-node (cadr bt) (bintree-add (caddr bt) num) (bintree-add (cadddr bt) num))))

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define symList? 
  (lambda (lst) 
    (if (null? lst) #t
        (if (symbol? (car lst)) (symList? (cdr lst)) 
            #f 
            ))))

(define letBasicAssignment?
  (lambda (lst)
    (if (null? lst) #t
        (if (not (list? lst)) #f
            (if (not (> (length lst) 1)) #f
                (if (not (symbol? (car lst))) #f
                    (if (not (expression? (cadr lst))) #f (letBasicAssignment? (cdr lst))
                        )))))))

(define (lit-exp? data)
  (or (number? data)
      (string? data)
      (symbol? data)
      (boolean? data)
      (and (list? data) (equal? (car data) 'quote))))

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data lit-exp?)]
  [lambda-exp
   (id symList?)
   (body expression?)]
  [let-exp-wo-body
   (assignment letBasicAssignment?)]
  [let-exp 
   (assignment letBasicAssignment?)
   (body expression?)]
  [if-exp
   (condition expression?)
   (true expression?)
   (false expression?)]
  [set-exp
   (id var-exp?)
   (value expression?)]
  [app-exp
   (rator expression?)
   (rand expression?)])

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(list? datum)
       (cond
         [(eqv? (car datum) 'lambda) (if (>= (length datum) 3) (if (symList? (2nd datum)) (lambda-exp (2nd datum) (parse-exp (3rd datum))) (error 'parse-exp "list of variables must consist of symbols: ~s" datum)) (error 'parse-exp "not enough bodies in lambda exp: ~s" datum))]
         [(eqv? (car datum) 'let) (if (letBasicAssignment? (2nd datum)) (if (= 2 (length datum)) (let-exp-wo-body (2nd datum)) (let-exp (2nd datum) (parse-exp (3rd datum)))) (error 'parse-exp "variable assignment is wrong: ~s" datum))]
         [(eqv? (car datum) 'if) (if (and (= (length datum) 4) (lit-exp? (2nd datum))) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum))) (error 'parse-exp "wrong if statement format: ~s" datum))]
         [(eqv? (car datum) 'set!) (if (and (= (length datum) 3) (symbol? (2nd datum))) (set-exp (var-exp (2nd datum)) (parse-exp (3rd datum))) (error 'parse-exp "wrong set! statement format: ~s" datum))]
         [else (app-exp (parse-exp (1st datum))
                        (parse-exp (2nd datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
  (lambda (exp)
    (nyi)))

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))