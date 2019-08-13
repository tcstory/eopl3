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
    (expression ("proc" "(" (separated-list my-identifier ",") ")" expression) proc-exp)
    (expression ("letrec" my-identifier "(" (arbno my-identifier)  ")" "=" expression "in" expression) letrec-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno my-identifier "=" expression) "in" expression) let-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("try" expression "catch" "(" my-identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)))

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
  (emptypair-val)
  (proc-val
   (proc proc?)))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

(define (apply-procedure/k proc1 vals saved-cont hand-cont)
  (cases proc proc1
    (procedure (vars body saved-env)
               (value-of/k body
                           (extend-env* vars vals saved-env)
                           saved-cont
                           hand-cont))))

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

(define (end-cont)
  (lambda (val)
    val))

(define (zero1-cont saved-cont)
  (lambda (val)
    (apply-cont saved-cont (bool-val (zero? (expval->num val))))))

(define (let-exp-cont vars exps body binding-eval-env body-eval-env saved-cont hand-cont)
  (lambda (val)
    (let ((my-env (extend-env (car vars) val body-eval-env)))
      (if (= (length vars) 1)
          (value-of/k body my-env saved-cont hand-cont)
          (value-of/k (car exps) binding-eval-env
                      (let-exp-cont (cdr vars) (cdr exps) body binding-eval-env body-eval-env saved-cont hand-cont)
                      hand-cont)))))
          

(define (if-test-cont exp2 exp3 saved-env saved-cont hand-cont)
  (lambda (val)
    (if (expval->bool val)
        (value-of/k exp2 saved-env saved-cont hand-cont)
        (value-of/k exp3 saved-env saved-cont hand-cont))))

(define (diff1-cont exp2 saved-env saved-cont hand-cont)
  (lambda (val)
    (value-of/k exp2 saved-env (diff2-cont val saved-env saved-cont) hand-cont)))


(define (diff2-cont val1 saved-env saved-cont)
  (lambda (val2)
    (let ((num1 (expval->num val1))
          (num2 (expval->num val2)))
      (apply-cont saved-cont (num-val (- num1 num2))))))

(define (rator-cont rands saved-env saved-cont hand-cont)
  (lambda (val)
    (value-of/k (car rands)
                saved-env
                (rands-cont val (cdr rands) `() saved-env saved-cont hand-cont)
                hand-cont)))

(define (rands-cont rator rands rand-vals saved-env saved-cont hand-cont)
  (lambda (val)
    (if (null? rands)
        (let ((proc1 (expval->proc rator)))
          (apply-procedure/k proc1 (append rand-vals (list val)) saved-cont hand-cont))
        (value-of/k (car rands) saved-env
                    (rands-cont rator (cdr rands) (append rand-vals (list val)) saved-env saved-cont hand-cont)
                    hand-cont))))

(define (try-cont saved-cont)
  (lambda (val)
    (apply-cont saved-cont val)))

(define (raise1-cont saved-cont hand-cont)
  (lambda (val)
    (apply-handler val hand-cont)))

(define (default-hand-cont)
  (lambda (val)
    (eopl:printf "report-uncaught-exception.~%")))


(define (apply-cont cont val) (cont val))


(define (apply-handler val cont) (cont val))

           

(define (run string)
  (value-of-program (scan&parse string)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1) (value-of/k exp1 (init-env) (end-cont) (default-hand-cont)))))

(define (value-of/k exp env cont hand-cont)
  (cases expression exp
    (const-exp (num) (apply-cont cont (num-val num)))
    (var-exp (var) (apply-cont cont (apply-env env var)))
    (proc-exp (vars body)
              (apply-cont cont
                          (proc-val (procedure vars body env))))
    (letrec-exp (p-name p-vars p-body let-body)
                (value-of/k let-body
                            (extend-env-rec p-name p-vars p-body env)
                            cont
                            hand-cont))
    (zero?-exp (exp1)
               (value-of/k exp1 env (zero1-cont cont) hand-cont))
    (if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env (if-test-cont exp2 exp3 env cont hand-cont) hand-cont))
    (let-exp (vars exps body)
             (value-of/k (car exps) env (let-exp-cont vars (cdr exps) body env env cont hand-cont) hand-cont))
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont hand-cont) hand-cont))
    (call-exp (rator rands)
              (value-of/k rator env
                          (rator-cont rands env cont hand-cont)
                          hand-cont))
    (try-exp (exp1 var handler-exp)
             (value-of/k exp1 env
                         cont
                         (lambda (val)
                           (value-of/k handler-exp
                                       (extend-env var val env)
                                       cont
                                       hand-cont))))
    (raise-exp (exp1)
               (value-of/k exp1 env
                           (raise1-cont cont hand-cont)
                           hand-cont))))
