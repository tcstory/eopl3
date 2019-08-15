#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number)
    (my-identifier (letter (arbno (or digit letter "_"))) symbol)))

(define the-grammar
  '((program (tf-exp) a-program)
    (simple-exp (my-number) const-exp)
    (simple-exp (my-identifier) var-exp)
    (simple-exp ("-" "(" simple-exp "," simple-exp ")") cps-diff-exp)
    (simple-exp ("zero?" "(" simple-exp ")") cps-zero?-exp)
    (simple-exp ("proc" "(" (separated-list my-identifier ",") ")" tf-exp) cps-proc-exp)
    (tf-exp (simple-exp) simple-exp->exp)
    (tf-exp ("let" my-identifier "=" simple-exp "in" tf-exp) cps-let-exp)
    (tf-exp ("letrec" (arbno my-identifier "(" (separated-list my-identifier ",") ")" "=" tf-exp) "in" tf-exp) cps-letrec-exp)
    (tf-exp ("if" simple-exp "then" tf-exp "else" tf-exp) cps-if-exp)
    (tf-exp ("(" simple-exp (arbno simple-exp) ")") cps-call-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define identifier? symbol?)

(define reference? integer?)

(define empty? null?)

(define the-store 'undefined)

(define (empty-store) `()) 

(define (init-store)
  (set! the-store (empty-store)))

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store (letrec ((loop (lambda (the-store0 ref0)
                                   (if (= ref0 0)
                                       (cons val (cdr the-store0))
                                       (cons (car the-store0) (loop (cdr the-store0) (- ref0 1)))))))
                    (loop the-store ref))))

(define (report-no-binding-found search-var)
  (eopl:error `apply-env "No binding for ~s" search-var))

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var identifier?)
   (saved-val reference?)
   (saved-env environment?))
  (extend-env-rec
   (p-name identifier?)
   (p-vars (list-of identifier?))
   (p-body tf-exp?)
   (saved-env environment?)))


(define (apply-env env search-var)
  (my-apply-env env search-var env))

(define (my-apply-env env search-var orig-env)
  (cases environment env
    (empty-env () (report-no-binding-found search-var))
    (extend-env (saved-var saved-val saved-env)
                (if (eqv? search-var saved-var)
                    saved-val
                    (apply-env saved-env search-var)))
    (extend-env-rec (p-name p-vars p-body saved-env)
                    (if (eqv? search-var p-name)
                        (newref (proc-val (procedure p-vars p-body orig-env)))
                        (my-apply-env saved-env search-var orig-env)))))

(define (extend-env-rec* p-names p-vars p-bodies saved-env)
  (if (null? p-names)
      saved-env
      (extend-env-rec*
       (cdr p-names)
       (cdr p-vars)
       (cdr p-bodies)
       (extend-env-rec (car p-names) (car p-vars) (car p-bodies) saved-env))))
                                       

(define (init-env)
  (extend-env
   'i (newref (num-val 1))
   (extend-env
    'v (newref (num-val 5))
    (extend-env
     'x (newref (num-val 10)) (empty-env)))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body tf-exp?)
   (saved-env environment?)))

(define (apply-procedure/k proc1 vals)
  (cases proc proc1
    (procedure (vars body saved-env)
               (value-of/k body
                           (extend-env* vars vals saved-env)))))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr vals) (extend-env (car vars) (newref (car vals)) env))))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (report-expval-extractor-error 'proc val))))

(define report-expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


(define (run string)
  (value-of-program 3 (scan&parse string)))

(define (value-of-program timeslice pgm)
  (init-store)
  (cases program pgm
    (a-program (exp1) (value-of/k exp1 (init-env)))))

(define (value-of/k exp env)
  (cases tf-exp exp
    (simple-exp->exp (simple1)
                     (value-of-simple-exp simple1 env))
    (cps-let-exp (var exp1 body)
                 (let ((val (value-of-simple-exp exp1 env)))
                   (value-of/k body
                               (extend-env var (newref val) env))))
    (cps-letrec-exp (p-names p-varss p-bodies let-body)
                    (value-of/k let-body
                                (extend-env-rec* p-names p-varss p-bodies env)))
    (cps-if-exp (simple1 body1 body2)
                (if (expval->bool (value-of-simple-exp simple1 env))
                    (value-of/k body1 env)
                    (value-of/k body2 env)))
    (cps-call-exp (rator rands)
                  (let ((rator-proc
                         (expval->proc (value-of-simple-exp rator env)))
                        (rand-vals
                         (map
                          (lambda (simple)
                            (value-of-simple-exp simple env))
                          rands)))
                    (apply-procedure/k rator-proc rand-vals)))))

(define (value-of-simple-exp exp env)
  (cases simple-exp exp
    (const-exp (num) (num-val num))
    (var-exp (var) (deref (apply-env env var)))
    (cps-diff-exp (exp1 exp2)
                  (let ((num1 (expval->num (value-of-simple-exp exp1 env)))
                        (num2 (expval->num (value-of-simple-exp exp2 env))))
                    (num-val (- num1 num2))))
    (cps-zero?-exp (exp1)
                   (let ((val1 (expval->num (value-of-simple-exp exp1 env))))
                     (bool-val (zero? val1))))
    (cps-proc-exp (vars body)
                  (proc-val (procedure vars body env)))))


; (run "letrec fn(dummy) =  22 in (fn 10)")
; (run "let x = 5 in x")

;(run "
;letrec
;even(x) = if zero?(x) then 1 else (odd -(x,1))
;odd(x) = if zero?(x) then 0 else (even -(x,1))
;in (odd 13)
;")