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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)))

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
  (emptypair-val)
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

(define (get-pair-car val)
  (cases expval val
    (pair-val (car-val cdr-val) car-val)
    (else (report-expval-extractor-error 'pair val))))

(define (get-pair-cdr val)
  (cases expval val
    (pair-val (car-val cdr-val) cdr-val)
    (else (report-expval-extractor-error 'pair val))))

(define (is-null? val)
  (cases expval val
    (emptypair-val () (bool-val #t))
    (else (bool-val #f))))

;; 这个函数我没想到, 看了别人的答案才明白的, 我之前花了挺长时间在思考如何把 pair 给串联起来...
(define (list->pairs vals)
  (if (null? vals)
      (emptypair-val)
      (pair-val (car vals)
                (list->pairs (cdr vals)))))

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
  (pair-car-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?))
  (pair-cdr-cont
   (car-val expval?)
   (cont continuation?))
  (get-pair-car-cont
   (cont continuation?))
  (get-pair-cdr-cont
   (cont continuation?))
  (null?-cont
   (cont continuation?))
  (list-exp-cont
   (vals (list-of expval?))
   (exps (list-of expression?))
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
    (rator-cont (rand saved-env saved-cont)
                (value-of/k rand saved-env
                            (rand-cont val saved-cont)))
    (rand-cont (rator saved-cont)
               (let ((proc1 (expval->proc rator)))
                 (apply-procedure/k proc1 val saved-cont)))
    (pair-car-cont (exp2 saved-env saved-cont)
                   (value-of/k exp2 saved-env
                               (pair-cdr-cont val saved-cont)))
    (pair-cdr-cont (car-val saved-cont)
                   (apply-cont saved-cont
                               (pair-val car-val val)))
    (get-pair-car-cont (saved-cont)
                       (apply-cont saved-cont (get-pair-car val)))
    (get-pair-cdr-cont (saved-cont)
                       (apply-cont saved-cont (get-pair-cdr val)))
    (null?-cont (saved-cont)
                (apply-cont saved-cont (is-null? val)))
    (list-exp-cont (vals exps saved-env saved-cont)
                   (let ((new-vals (append vals (list val))))
                     (if (null? exps)
                         (apply-cont saved-cont (list->pairs new-vals))
                         (value-of/k (car exps) saved-env
                                     (list-exp-cont new-vals
                                                    (cdr exps)
                                                    saved-env
                                                    saved-cont)))))))



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
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont)))
    (call-exp (rator rand)
              (value-of/k rator env
                          (rator-cont rand env cont)))
    (cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (pair-car-cont exp2 env cont)))
    (emptylist-exp ()
                   (apply-cont cont (emptypair-val)))
    (car-exp (exp1)
             (value-of/k exp1 env
                         (get-pair-car-cont cont)))
    (cdr-exp (exp1)
             (value-of/k exp1 env
                         (get-pair-cdr-cont cont)))
    (null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont)))
    (list-exp (exps)
              (value-of/k (car exps) env
                          (list-exp-cont (list) (cdr exps) env cont)))))