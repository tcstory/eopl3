#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number) 
    (my-identifier (letter (arbno (or digit letter))) symbol)))

(define the-grammar
  '((program (expression) a-program)
    (expression (my-number) const-exp)
    (expression (my-identifier) var-exp)
    (expression ("proc" "("  (separated-list my-identifier ",") ")" expression) proc-exp)
    (expression ("letrec" my-identifier "(" (separated-list my-identifier ",")  ")" "=" expression "in" expression) letrec-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" my-identifier "=" expression "in" expression) let-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define identifier? symbol?)

(define (report-no-binding-found search-var)
  (eopl:error `apply-env "No binding for ~s" search-var))

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var identifier?)
   (saved-val expval?)
   (saved-env environment?))
  (extend-env-rec
   (p-name identifier?)
   (p-vars (list-of identifier?))
   (p-body expression?)
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
                        (proc-val (procedure p-vars p-body orig-env))
                        (my-apply-env saved-env search-var orig-env)))))
                                       

(define (init-env)
  (extend-env
   'i (num-val 1)
   (extend-env
    'v (num-val 5)
    (extend-env
     'x (num-val 10) (empty-env)))))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptylist-val)
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

(define (apply-procedure/k)
  (cases proc g-proc
    (procedure (vars body saved-env)
               (set! g-exp body)
               ;; 用 g-env 替换掉 saved-env 就能实现了, 但是题目的 hint 里面说了一大堆,
               ;; 但我没看懂是啥意思
               (set! g-env (extend-env* vars g-val g-env))
               (value-of/k))))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))

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

(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?))
  (rator-cont
   (rands (list-of expression?))
   (env environment?)
   (cont continuation?))
  (rands-cont
   (rator expval?)
   (rands (list-of expression?))
   (rand-vals (list-of expval?))
   (cont continuation?)))


(define (apply-cont)
  (cases continuation g-cont
    (end-cont ()
              (begin
                (eopl:printf "End of computation.~%")
                g-val))
    (zero1-cont (saved-cont)
                (set! g-val (bool-val (zero? (expval->num g-val))))
                (set! g-cont saved-cont)
                (apply-cont))
    (let-exp-cont (var body saved-env saved-cont)
                  (set! g-exp body)
                  (set! g-env (extend-env var g-val saved-env))
                  (set! g-cont saved-cont)
                  (value-of/k))
    (if-test-cont (exp2 exp3 saved-env saved-cont)
                  (set! g-env saved-env)
                  (set! g-cont saved-cont)
                  (if (expval->bool g-val)
                      (set! g-exp exp2)
                      (set! g-exp exp3))
                  (value-of/k))
    (diff1-cont (exp2 saved-env saved-cont)
                (set! g-exp exp2)
                (set! g-env saved-env)
                (set! g-cont (diff2-cont g-val saved-cont))
                (value-of/k))
    (diff2-cont (val1 saved-cont)
                (set! g-cont saved-cont)
                (let ((num1 (expval->num val1))
                      (num2 (expval->num g-val)))
                  (set! g-val (num-val (- num1 num2))))
                (apply-cont))
    (rator-cont (rands saved-env saved-cont)
                (set! g-env saved-env)
                (set! g-exp (car rands))
                (set! g-cont (rands-cont g-val (cdr rands) `() saved-cont))
                (value-of/k))
    (rands-cont (rator rands rand-vals saved-cont)
                (if (null? rands)
                    (begin
                      (set! g-val (append rand-vals (list g-val)))
                      (let ((proc1 (expval->proc rator)))
                        (set! g-cont saved-cont)
                        (set! g-proc proc1)
                        (apply-procedure/k)))
                    (begin
                      (set! g-exp (car rands))
                      (set! g-cont (rands-cont rator
                                               (cdr rands)
                                               (append rand-vals (list g-val))
                                               saved-cont))
                      (value-of/k))))))

(define g-exp 'undefined)
(define g-env 'undefined)
(define g-cont 'undefined)
(define g-val 'undefined)
(define g-proc 'undefined)

(define (run string)
  (value-of-program (scan&parse string)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1)
               (set! g-cont (end-cont))
               (set! g-exp exp1)
               (set! g-env (init-env))
               (value-of/k))))

(define (value-of/k)
  (cases expression g-exp
    (const-exp (num)
               (set! g-val (num-val num))
               (apply-cont))
    (var-exp (var)
             (set! g-val (apply-env g-env var))
             (apply-cont))
    (proc-exp (vars body)
              (set! g-val (proc-val (procedure vars body g-env)))
              (apply-cont))
    (letrec-exp (p-name p-vars p-body let-body)
                (set! g-env (extend-env-rec p-name p-vars p-body g-env))
                (set! g-exp let-body)
                (value-of/k))
    (zero?-exp (exp1)
               (set! g-cont (zero1-cont g-cont))
               (set! g-exp exp1)
               (value-of/k))
    (if-exp (exp1 exp2 exp3)
            (set! g-cont (if-test-cont exp2 exp3 g-env g-cont))
            (set! g-exp exp1)
            (value-of/k))
    (let-exp (var exp1 body)
             (set! g-cont (let-exp-cont var body g-env g-cont))
             (set! g-exp exp1)
             (value-of/k))
    (diff-exp (exp1 exp2)
              (set! g-exp exp1)
              (set! g-cont (diff1-cont exp2 g-env g-cont))
              (value-of/k))
    (call-exp (rator rands)
              (set! g-exp rator)
              (set! g-cont (rator-cont rands g-env g-cont))
              (value-of/k))))

;; (run "let aa = 5 in let fn = proc(n) aa in let aa = 4 in (fn 0)")