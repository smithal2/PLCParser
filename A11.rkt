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

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data number?)]
  [lambda-exp
   (id symList?)
   (body expression?)]
  [let-exp 
   (assignment letBasicAssignment?)
   (body expression?)]
  [app-exp
   (rator expression?)
   (rand expression?)])

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'lambda) (if (>= (length datum) 3) (lambda-exp (2nd  datum) (parse-exp (3rd datum))) (error 'parse-exp "not enough bodies in lambda exp" datum))]
         [(eqv? (car datum) 'let) (let-exp (2nd datum) (parse-exp (3rd datum)))]
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
