#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number) 
    (my-identifier (letter (arbno (or digit letter))) symbol)))

(define the-grammar
  '((program (expression) a-program)
    (expression (my-identifier) var-exp)
    (expression ("proc" "(" my-identifier ")" expression) proc-exp)
    (expression (my-number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" my-identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("%lexref" my-number) nameless-var-exp)
    (expression ("%let" expression "in" expression) nameless-let-exp)
    (expression ("%lexproc" expression) nameless-proc-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (proc-val
   (proc proc?)))

(define (cond-val exps1 exps2 nameless-env)
  (cond ((null? exps1)
         (eopl:error 'cond-val "No condition got into #t"))
        ((equal? #t (expval->bool (value-of (car exps1) nameless-env)))
         (value-of (car exps2) nameless-env))
        (else (cond-val (cdr exps1) (cdr exps2) nameless-env))))

(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-nameless-env nameless-environment?)))

(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (eopl:error 'report-expval-extractor-error-num val))))

(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (eopl:error 'report-expval-extractor-error-bool val))))

(define (expval->proc val)
  (cases expval val
    (proc-val (proc) proc)
    (else (eopl:error 'report-expval-extractor-error-proc val))))

(define (nameless-environment? x)
  ((list-of expval?) x))

(define (empty-nameless-env)
  '())

(define (extend-nameless-env val nameless-env)
  (cons val nameless-env))

(define (apply-nameless-env nameless-env n)
  (list-ref nameless-env n))

(define (init-nameless-env)
  (extend-nameless-env
   (num-val 1)
   (extend-nameless-env
    (num-val 5)
    (extend-nameless-env
     (num-val 10) (empty-nameless-env)))))

(define (empty-senv)
  '())

(define (extend-senv var senv)
  (cons var senv))

(define (apply-senv senv var)
  (cond
    ((null? senv)
     (eopl:error 'report-unbound-var var))
    ((eqv? var (car senv))
     0)
    (else
     (+ 1 (apply-senv (cdr senv) var)))))

(define (init-senv)
  (extend-senv 'i
               (extend-senv 'v
                            (extend-senv 'x
                                         (empty-senv)))))

(define (translation-of-program pgm)
  (cases program pgm
    (a-program (exp)
               (a-program
                (translation-of exp (init-senv))))))

(define (translation-of exp senv)
  (cases expression exp
    (const-exp (num) (const-exp num))
    (diff-exp (exp1 exp2)
              (diff-exp
               (translation-of exp1 senv)
               (translation-of exp2 senv)))
    (zero?-exp (exp)
               (zero?-exp
                (translation-of exp senv)))
    (if-exp (exp1 exp2 exp3)
            (if-exp
             (translation-of exp1 senv)
             (translation-of exp2 senv)
             (translation-of exp3 senv)))
    (var-exp (var)
             (nameless-var-exp
              (apply-senv senv var)))
    (let-exp (var exp1 body)
             (nameless-let-exp
              (translation-of exp1 senv)
              (translation-of body
                              (extend-senv var senv))))
    (proc-exp (var body)
              (nameless-proc-exp
               (translation-of body
                               (extend-senv var senv))))
    (call-exp (rator rand)
              (call-exp
               (translation-of rator senv)
               (translation-of rand senv)))
    (cond-exp (exps1 exps2)
              (cond-exp
               (map (lambda (item) (translation-of item senv)) exps1)
               (map (lambda (item) (translation-of item senv)) exps2)))
    (else
     (eopl:error 'report-invalid-source-expression exp))))

(define (value-of exp nameless-env)
  (cases expression exp
    (const-exp (num) (num-val num))
    (diff-exp (exp1 exp2)
              (let ((num1 (expval->num (value-of exp1 nameless-env)))
                    (num2 (expval->num (value-of exp2 nameless-env))))
                (num-val (- num1 num2))))
    (zero?-exp (exp1)
               (let ((num1 (expval->num (value-of exp1 nameless-env))))
                 (if (zero? num1)
                     (bool-val #t)
                     (bool-val #f))))
    (if-exp (exp1 exp2 exp3)
            (let ((val1 (value-of exp1 nameless-env)))
              (if (expval->bool val1)
                  (value-of exp2 nameless-env)
                  (value-of exp3 nameless-env))))
    (call-exp (exp1 arg)
              (apply-procedure
               (expval->proc (value-of exp1 nameless-env))
               (value-of arg nameless-env)))
    (nameless-var-exp (n)
                      (apply-nameless-env nameless-env n))
    (nameless-let-exp (exp body)
                      (let ((val (value-of exp nameless-env)))
                        (value-of body
                                  (extend-nameless-env val nameless-env))))
    (nameless-proc-exp (body)
                       (proc-val
                        (procedure body nameless-env)))
    (cond-exp (exps1 exps2)
              (cond-val exps1 exps2 nameless-env))
    (else
     (eopl:error 'report-invalid-translated-expression exp))))

(define (apply-procedure proc1 val)
  (cases proc proc1
    (procedure (body saved-nameless-env)
               (value-of body
                         (extend-nameless-env val saved-nameless-env)))))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (exp)
               (value-of exp (init-nameless-env)))))

(define (run1 string)
   (translation-of-program
    (scan&parse string)))

(define (run2 string)
  (value-of-program
   (translation-of-program
    (scan&parse string))))