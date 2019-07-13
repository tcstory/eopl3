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
    (expression ("proc" "(" my-identifier ")" expression) proc-exp)
    (expression ("letrec" my-identifier "(" my-identifier  ")" "=" expression "in" expression) letrec-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" my-identifier "=" expression "in" expression) let-exp)
    (expression ("let2" my-identifier "=" expression  my-identifier "=" expression "in" expression) let2-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("(" expression expression ")") call-exp)))

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
   (p-var identifier?)
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
    (extend-env-rec (p-name p-var p-body saved-env)
                    (if (eqv? search-var p-name)
                        (proc-val (procedure p-var p-body orig-env))
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
   (var identifier?)
   (body expression?)
   (saved-env environment?)))

(define (apply-procedure/k proc1 val cont)
  (cases proc proc1
    (procedure (var body saved-env)
               (value-of/k body
                           (extend-env var val saved-env)
                           cont))))

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
   (rand expression?)
   (env environment?)
   (cont continuation?))
  (rand-cont
   (rator expval?)
   (cont continuation?))
  (let2-exp-cont1
   (var1 identifier?)
   (var2 identifier?)
   (exp2 expression?)
   (body expression?)
   (env environment?)
   (cont continuation?))
  (let2-exp-cont2
   (var2 identifier?)
   (body expression?)
   (env environment?)
   (cont continuation?)))


(define (apply-cont cont val)
  (cases continuation cont
    (end-cont ()
              (begin
                (eopl:printf "End of computation.~%")
                val))
    (zero1-cont (saved-cont)
                (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
    (let-exp-cont (var body saved-env saved-cont)
                  (value-of/k body
                              (extend-env var val saved-env) saved-cont))
    (if-test-cont (exp2 exp3 saved-env saved-cont)
                  (if (expval->bool val)
                      (value-of/k exp2 saved-env saved-cont)
                      (value-of/k exp3 saved-env saved-cont)))
    (diff1-cont (exp2 saved-env saved-cont)
                (value-of/k exp2 saved-env (diff2-cont val saved-cont)))
    (diff2-cont (val1 saved-cont)
                (let ((num1 (expval->num val1))
                      (num2 (expval->num val)))
                  (apply-cont saved-cont (num-val (- num1 num2)))))
    (rator-cont (rand env cont)
                (value-of/k rand env
                            (rand-cont val cont)))
    (rand-cont (rator cont)
               (let ((proc1 (expval->proc rator)))
                 (apply-procedure/k proc1 val cont)))
    (let2-exp-cont1 (var1 var2 exp2 body env cont)
                    (value-of/k exp2
                                env
                                (let2-exp-cont2 var2 body (extend-env var1 val env) cont)))
    (let2-exp-cont2 (var2 body env cont)
                    (value-of/k body
                                (extend-env var2 val env)
                                cont))))

(define (run string)
  (value-of-program (scan&parse string)))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp1) (value-of/k exp1 (init-env) (end-cont)))))

(define (value-of/k exp env cont)
  (cases expression exp
    (const-exp (num) (apply-cont cont (num-val num)))
    (var-exp (var) (apply-cont cont (apply-env env var)))
    (proc-exp (var body)
              (apply-cont cont
                          (proc-val (procedure var body env))))
    (letrec-exp (p-name p-var p-body let-body)
                (value-of/k let-body
                            (extend-env-rec p-name p-var p-body env)
                            cont))
    (zero?-exp (exp1)
               (value-of/k exp1 env (zero1-cont cont)))
    (if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
    (let-exp (var exp1 body)
             (value-of/k exp1 env (let-exp-cont var body env cont)))
    (let2-exp (var1 exp1 var2 exp2 body)
              (value-of/k exp1 env
                          (let2-exp-cont1 var1 var2 exp2 body env cont)))
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont)))
    (call-exp (rator rand)
              (value-of/k rator env
                          (rator-cont rand env cont)))))