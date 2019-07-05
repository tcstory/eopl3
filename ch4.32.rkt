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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno my-identifier "=" expression) "in" expression) let-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("equal?" "(" expression "," expression ")") equal?-exp)
    (expression ("greater?" "(" expression "," expression ")") greater?-exp)
    (expression ("less?" "(" expression "," expression ")") less?-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("let*" (arbno my-identifier "=" expression) "in" expression) let*-exp)
    (expression ("unpack" (arbno my-identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (separated-list my-identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letproc" my-identifier "=" "(" my-identifier ")" expression "in" expression) let-proc-exp)
    (expression ("letrec" (arbno my-identifier "(" (separated-list my-identifier ",") ")" "=" expression) "in" expression) let-rec-exp)
    (expression ("set" my-identifier "=" expression) assign-exp)
    (expression ("begin" (separated-list expression ";") "end") begin-exp)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define identifier? symbol?)

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
   (p-body expression?)
   (saved-env environment?)))

(define (empty-store) '())

(define the-store 'unitialized)

(define (get-store) the-store)

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define reference?
  (lambda (v)
    (integer? v)))

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store
        (letrec ((loop (lambda (the-store1 ref1)
                         (cond
                           ((null? the-store1) (eopl:error 'report-invalid-reference))
                           ((eqv? 0 ref1)
                            (cons val (cdr the-store1)))
                           (else
                            (cons
                             (car the-store1)
                             (loop (cdr the-store1) (- ref1 1))))))))
          (loop the-store ref))))


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
                                       
(define (extend-env-rec* p-names p-vars p-bodys saved-env)
  (if (null? p-names)
      saved-env
      (extend-env-rec*
       (cdr p-names)
       (cdr p-vars)
       (cdr p-bodys)
       (extend-env-rec (car p-names) (car p-vars) (car p-bodys) saved-env))))

(define (init-env)
  (extend-env
   'i (newref (num-val 1))
   (extend-env
    'v (newref (num-val 5))
    (extend-env
     'x (newref (num-val 10)) (empty-env)))))

(define-datatype program program?
  (a-program
   (exp1 expression?)))

(define-datatype expression expression?
  (const-exp
   (num number?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (zero?-exp
   (exp1 expression?))
  (if-exp
   (exp1 expression?)
   (exp2 expression?)
   (exp3 expression?))
  (var-exp
   (var identifier?))
  (let-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (minus-exp
   (exp expression?))
  (add-exp
   (exp1 expression?)
   (exp2 expression?))
  (mul-exp
   (exp1 expression?)
   (exp2 expression?))
  (div-exp
   (exp1 expression?)
   (exp2 expression?))
  (equal?-exp
   (exp1 expression?)
   (exp2 expression?))
  (greater?-exp
   (exp1 expression?)
   (exp2 expression?))
  (less?-exp
   (exp1 expression?)
   (exp2 expression?))
  (cons-exp
   (exp1 expression?)
   (exp2 expression?))
  (emptylist-exp)
  (car-exp (exp1 expression?))
  (cdr-exp (exp1 expression?))
  (null?-exp (exp1 expression?))
  (list-exp (exps (list-of expression?)))
  (cond-exp (exps1 (list-of expression?))
            (exps2 (list-of expression?)))
  (let*-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  (unpack-exp
   (vars (list-of identifier?))
   (exp expression?)
   (body expression?))
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  (call-exp
   (exp expression?)
   (args (list-of expression?)))
  (let-proc-exp
   (proc-name identifier?)
   (proc-var identifier?)
   (proc-body expression?)
   (let-body expression?))
  (let-rec-exp
   (p-names (list-of identifier?))
   (p-varss (list-of (list-of identifier?)))
   (p-bodys (list-of expression?))
   (let-body expression?))
  (assign-exp
   (var identifier?)
   (exp expression?))
  (begin-exp
    (exps (list-of expression?))))

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

(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (letrec ((loop (lambda (vars0 vals0 new-env)
                                  (if (null? vars0)
                                      (value-of body new-env)
                                      (loop (cdr vars0)
                                            (cdr vals0)
                                            (extend-env
                                             (car vars0)
                                             (car vals0)
                                             new-env))))))
                   (loop vars vals saved-env))))))

(define (cond-val exps1 exps2 env)
  (cond ((null? exps1)
         (eopl:error 'cond-val "No condition got into #t"))
        ((equal? #t (expval->bool (value-of (car exps1) env)))
         (value-of (car exps2) env))
        (else (cond-val (cdr exps1) (cdr exps2) env))))

(define (let-val vars exps body old-env new-env)
  (cond ((null? vars) (value-of body new-env))
        (else (let ((var0 (car vars))
                    (val0 (value-of (car exps) old-env)))
                (let-val
                 (cdr vars)
                 (cdr exps)
                 body
                 old-env
                 (extend-env var0 (newref val0) new-env))))))

(define (let*-val vars exps body env)
  (cond ((null? vars) (value-of body env))
        (else (let ((var0 (car vars))
                    (val0 (value-of (car exps) env)))
                (let*-val
                 (cdr vars)
                 (cdr exps)
                 body
                 (extend-env var0 (newref val0) env))))))

(define (unpack-val vars exp body env)
  (let ((lst (value-of exp env)))
    (letrec ((loop (lambda (vars0 lst0 env0)
                     (if (null? vars0)
                         (value-of body env0)
                         (loop (cdr vars0)
                               (expval->cdr lst0)
                               (extend-env (car vars0) (expval->car lst0) env0))))))
      (loop vars lst env))))

(define (list-val exps env)
  (if (null? exps)
      (emptylist-val)
      (pair-val (value-of (car exps) env)
                (list-val (cdr exps) env))))

(define (begin-val exps env)
  (cond
    ((null? exps) (eopl:error 'begin-val "begin-val"))
    ((= 1 (length exps))
     (value-of (car exps) env))
    (else
     (begin
       (value-of (car exps) env)
       (begin-val (cdr exps) env)))))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))))

(define (expval->car val)
  (cases expval val
    (pair-val (car cdr) car)
    (else (report-expval-extractor-error 'car val))))

(define (expval->cdr val)
  (cases expval val
    (pair-val (car cdr) cdr)
    (else (report-expval-extractor-error 'cdr val))))

(define (expval->null? val)
  (cases expval val
    (emptylist-val () (bool-val #t))
    (else (bool-val #f))))

(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (report-expval-extractor-error 'proc val))))

(define report-expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))

(define (value-of-operand exp env)
  (cases expression exp
    (var-exp (var) (apply-env env var))
    (else (newref (value-of exp env)))))

  (define (run string)
    (value-of-program (scan&parse string)))

  (define (value-of-program pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (exp1) (value-of exp1 (init-env)))))

  (define (value-of exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ((num1 (expval->num (value-of exp1 env)))
                      (num2 (expval->num (value-of exp2 env))))
                  (num-val (- num1 num2))))
      (zero?-exp (exp1)
                 (let ((num1 (expval->num (value-of exp1 env))))
                   (if (zero? num1)
                       (bool-val #t)
                       (bool-val #f))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      (let-exp (vars exps body)
               (let-val vars exps body env env))
      (minus-exp (exp)
                 (let ((val (value-of exp env)))
                   (num-val (- 0 (expval->num val)))))
      (add-exp (exp1 exp2)
               (let ((num1 (expval->num (value-of exp1 env)))
                     (num2 (expval->num (value-of exp2 env))))
                 (num-val (+ num1 num2))))  
      (mul-exp (exp1 exp2)
               (let ((num1 (expval->num (value-of exp1 env)))
                     (num2 (expval->num (value-of exp2 env))))
                 (num-val (* num1 num2))))
      (div-exp (exp1 exp2)
               (let ((num1 (expval->num (value-of exp1 env)))
                     (num2 (expval->num (value-of exp2 env))))
                 (num-val (/ num1 num2))))
      (equal?-exp (exp1 exp2)
                  (let ((num1 (expval->num (value-of exp1 env)))
                        (num2 (expval->num (value-of exp2 env))))
                    (bool-val (= num1 num2))))
      (greater?-exp (exp1 exp2)
                    (let ((num1 (expval->num (value-of exp1 env)))
                          (num2 (expval->num (value-of exp2 env))))
                      (bool-val (> num1 num2))))
      (less?-exp (exp1 exp2)
                 (let ((num1 (expval->num (value-of exp1 env)))
                       (num2 (expval->num (value-of exp2 env))))
                   (bool-val (< num1 num2))))
      (cons-exp (exp1 exp2)
                (pair-val (value-of exp1 env)
                          (value-of exp2 env)))
      (emptylist-exp () (emptylist-val))
      (car-exp (exp1)
               (expval->car (value-of exp1 env)))
      (cdr-exp (exp1)
               (expval->cdr (value-of exp1 env)))
      (null?-exp (exp1)
                 (expval->null? (value-of exp1 env)))
      (list-exp (exps)
                (list-val exps env))
      (cond-exp (exps1 exps2)
                (cond-val exps1 exps2 env))
      (let*-exp (vars exps body)
                (let*-val vars exps body env))
      (unpack-exp (vars exp body)
                  (unpack-val vars exp body env))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (exp args)
                (apply-procedure
                 (expval->proc (value-of exp env))
                 (map (lambda (arg) (value-of-operand arg env)) args)))
      (let-proc-exp (proc-name proc-var proc-body let-body)
                    (value-of
                     let-body
                     (extend-env
                      proc-name
                      (proc-val (procedure proc-var proc-body env))
                      env)))
      (let-rec-exp (p-names p-varss p-bodys let-body)
                   (value-of let-body
                             (extend-env-rec* p-names p-varss p-bodys env)))
      (assign-exp (var exp1)
                  (begin
                    (setref!
                     (apply-env env var)
                     (value-of exp1 env))
                    (num-val 1)))
      (begin-exp (exps)
                 (begin-val exps env))))