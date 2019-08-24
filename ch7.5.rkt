#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number)
    (my-identifier (letter (arbno (or digit letter))) symbol)))

(define the-grammar
  '((program (expression) a-program)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (arbno type) "->" type ")") proc-type)
    (expression (my-number) const-exp)
    (expression (my-identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let"  (arbno my-identifier "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" (separated-list my-identifier ":" type ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" type my-identifier "(" (separated-list my-identifier ":" type ",") ")" "=" expression  "in" expression) letrec-exp)))


(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'type-of-expression
                "Rator not a proc type:~%~s~%had rator type ~s"
                rator
                (type-to-external-form rator-type))))

(define (check-equal-type! ty1 ty2 exp)
  (if (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp)
      empty))

(define (report-unequal-types ty1 ty2 exp)
  (eopl:error 'check-equal-type!
              "Types didn't match: ~s != ~a in ~%~a"
              (type-to-external-form ty1)
              (type-to-external-form ty2)
              exp))

(define (type-to-external-form ty)

  (if (pair? ty)
      (map type-to-external-form ty)
  (cases type ty
    (int-type () 'int)
    (bool-type () 'bool)
    (proc-type (arg-type result-type)
               (list
                (type-to-external-form arg-type)
                '->
                (type-to-external-form result-type))))))

(define identifier? symbol?)

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv
   (saved-var identifier?)
   (saved-val type?)
   (saved-tenv tenvironment?)))

(define (extend-tenv* vars types tenv)
  (if (null? vars)
      tenv
      (extend-tenv* (cdr vars) (cdr types) (extend-tenv (car vars) (car types) tenv))))

(define (apply-tenv tenv var)
  (cases tenvironment tenv
    (empty-tenv () (eopl:error `apply-env "No binding for ~s" var))
    (extend-tenv (saved-var saved-val saved-tenv)
                 (if (eqv? var saved-var)
                     saved-val
                     (apply-tenv saved-tenv var)))))


(define (init-tenv)
  (extend-tenv
   'i (int-type)
   (extend-tenv
    'v (int-type)
    (extend-tenv
     'x (int-type) (empty-tenv)))))


(define (let-val vars exps body tenv)
  (letrec ((loop (lambda (vars0 exps0 old-tenv new-tenv)
                 (if (null? vars0)
                     (type-of body new-tenv)
                     (loop
                      (cdr vars0)
                      (cdr exps0)
                      old-tenv
                      (extend-tenv (car vars0) (type-of (car exps0) old-tenv) new-tenv))))))
    (loop vars exps tenv tenv)))

(define (type-of-program pgm)
  (cases program pgm
    (a-program (exp1) (type-of exp1 (init-tenv)))))

(define (run string)
  (type-of-program (scan&parse string)))

(define (type-of exp tenv)
  (cases expression exp
    (const-exp (num) (int-type))
    (var-exp (var) (apply-tenv tenv var))
    (diff-exp (exp1 exp2)
              (let ((ty1 (type-of exp1 tenv))
                    (ty2 (type-of exp2 tenv)))
                (check-equal-type! ty1 (int-type) exp1)
                (check-equal-type! ty2 (int-type) exp2)
                (int-type)))
    (zero?-exp (exp1)
               (let ((ty1 (type-of exp1 tenv)))
                 (check-equal-type! ty1 (int-type) exp1)
                 (bool-type)))
    (if-exp (exp1 exp2 exp3)
            (let ((ty1 (type-of  exp1 tenv))
                  (ty2 (type-of  exp2 tenv))
                  (ty3 (type-of  exp3 tenv)))
              (check-equal-type! ty1 (bool-type) exp1)
              (check-equal-type! ty2 ty3 exp)
              ty2))
    (let-exp (vars exps body)
             (let-val vars exps body tenv))
    (proc-exp (vars var-types body)
              (let ((result-type
                     (type-of body
                              (extend-tenv* vars var-types tenv))))
                (proc-type var-types result-type)))
    (call-exp (rator rands)              
              (let ((rator-type (type-of rator tenv ))
                    (rand-types (map (lambda (item) (type-of item tenv )) rands)))
                (cases type rator-type
                  (proc-type (var-types result-type)
                             (begin
                               (check-equal-type! var-types rand-types rator)
                               result-type))
                  (else
                   (report-rator-not-a-proc-type rator-type rator)))))
    (letrec-exp (p-result-type p-name b-vars b-var-types p-body letrec-body)
                (let ((tenv-for-letrec-body
                       (extend-tenv
                        p-name
                        (proc-type b-var-types p-result-type)
                        tenv)))

                  (let ((p-body-type (type-of
                                      p-body
                                      (extend-tenv* b-vars b-var-types tenv-for-letrec-body))))
                    (check-equal-type! p-body-type p-result-type p-body)
                    (type-of letrec-body tenv-for-letrec-body ))))))
                  

;; (run "proc (f : (bool -> int)) proc (n : int) (f zero?(n))")

;; (run "letrec int fn(x:int) = -(x,1) in (fn 1)")

;; (run "letrec int fn(x:int,y:int) = -(x,y) in (fn 1 zero?(0))")

;; (run "letrec bool fn(x:bool) = x in (fn zero?(0))")