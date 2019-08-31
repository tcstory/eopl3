#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number)
    (my-identifier (letter (arbno (or digit letter))) symbol)))

(define the-grammar
  '((program ((arbno module-definition) expression) a-program)
    (module-definition ("module" my-identifier "interface" iface "body" module-body) a-module-definition)
    (iface ("[" (arbno decl) "]") simple-iface)
    (decl (my-identifier ":" type) val-decl)
    (module-body ("[" (arbno definition) "]") defns-module-body)
    (definition (my-identifier "=" expression) val-defn)
    (expression ("from" my-identifier "take" my-identifier) qualified-var-exp)
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

(define-datatype typed-module typed-module?
  (simple-module
   (bindings environment?)))

(define (lookup-qualified-var-in-env m-name var-name env)
  (let ((m-val (lookup-module-name-in-env m-name env)))
    (cases typed-module m-val
      (simple-module (bindings)
                     (apply-env bindings var-name)))))

(define (lookup-module-name-in-env m-name env)
  (cases environment env
    (empty-env () (report-no-binding-found m-name))
    (extend-env-with-module (saved-m-name saved-m-val saved-env)
                            (if (eqv? m-name saved-m-name)
                                saved-m-val
                                (lookup-module-name-in-env m-name saved-env)))
    (extend-env (saved-var saved-val saved-env)
                (lookup-module-name-in-env m-name saved-env))
    (extend-env-rec (p-name p-vars p-body saved-env)
                    (lookup-module-name-in-env m-name saved-env))))

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
   (saved-env environment?))
  (extend-env-with-module
   (m-name identifier?)
   (m-val typed-module?)
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
                        (my-apply-env saved-env search-var orig-env)))
    (extend-env-with-module (m-name m-val saved-env)
                            (if (eqv? m-name search-var)
                                m-val
                                (apply-env saved-env search-var)))))

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
                                             (newref
                                              (car vals0))
                                             new-env))))))
                   (loop vars vals saved-env))))))

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


;(define (type-let-val vars exps body tenv)
;  (letrec ((loop (lambda (vars0 exps0 old-tenv new-tenv)
;                   (if (null? vars0)
;                       (type-of body new-tenv)
;                       (loop
;                        (cdr vars0)
;                        (cdr exps0)
;                        old-tenv
;                        (extend-tenv (car vars0) (type-of (car exps0) old-tenv) new-tenv))))))
;    (loop vars exps tenv tenv)))

;(define (type-of-program pgm)
;  (cases program pgm
;    (a-program (exp1) (type-of exp1 (init-tenv)))))

;(define (run string)
;  (type-of-program (scan&parse string)))

(define (run string)
  (value-of-program (scan&parse string)))

(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (m-defns exp1)
               (value-of exp1
                         (add-module-defns-to-env m-defns (init-env))))))
(define (add-module-defns-to-env defns env)
  (if (null? defns)
      env
      (cases module-definition (car defns)
        (a-module-definition (m-name my-iface m-body)
                             (add-module-defns-to-env
                              (cdr defns)
                              (extend-env-with-module
                               m-name
                               (value-of-module-body m-body my-iface env)
                               env))))))

(define (value-of-module-body m-body my-iface env)
  (cases module-body m-body
    (defns-module-body (defns)
      (simple-module (defns-to-env defns my-iface (empty-env) env)))))

(define (defns-to-env defns my-iface env eval-env)
  (if (null? defns)
      env
      (cases definition (car defns)
        (val-defn (var exp1)
                  (let ((val (value-of exp1 eval-env)))
                    (let ((new-eval-env (extend-env var (newref val) eval-env)))
                      (if (var-in-interface? my-iface var)
                          (defns-to-env (cdr defns) my-iface (extend-env var (newref val) env) new-eval-env)
                          (defns-to-env (cdr defns) my-iface env new-eval-env))))))))


(define (var-in-interface? my-iface var)
  (cases iface my-iface
    (simple-iface (decls)
                  (letrec ((loop (lambda (decls0)
                                   (cond
                                     ((null? decls0) #f)
                                     ((eqv? var (val-decl->var (car decls0))) #t)
                                     (else (loop (cdr decls0)))))))
                    (loop decls)))))

(define (val-decl->var my-decl)
  (cases decl my-decl
    (val-decl (my-var my-type)
              my-var)))
                                       

;(define (type-of exp tenv)
;  (cases expression exp
;    (const-exp (num) (int-type))
;    (var-exp (var) (apply-tenv tenv var))
;    (diff-exp (exp1 exp2)
;              (let ((ty1 (type-of exp1 tenv))
;                    (ty2 (type-of exp2 tenv)))
;                (check-equal-type! ty1 (int-type) exp1)
;                (check-equal-type! ty2 (int-type) exp2)
;                (int-type)))
;    (zero?-exp (exp1)
;               (let ((ty1 (type-of exp1 tenv)))
;                 (check-equal-type! ty1 (int-type) exp1)
;                 (bool-type)))
;    (if-exp (exp1 exp2 exp3)
;            (let ((ty1 (type-of  exp1 tenv))
;                  (ty2 (type-of  exp2 tenv))
;                  (ty3 (type-of  exp3 tenv)))
;              (check-equal-type! ty1 (bool-type) exp1)
;              (check-equal-type! ty2 ty3 exp)
;              ty2))
;    (let-exp (vars exps body)
;             (type-let-val vars exps body tenv))
;    (proc-exp (vars var-types body)
;              (let ((result-type
;                     (type-of body
;                              (extend-tenv* vars var-types tenv))))
;                (proc-type var-types result-type)))
;    (call-exp (rator rands)              
;              (let ((rator-type (type-of rator tenv ))
;                    (rand-types (map (lambda (item) (type-of item tenv )) rands)))
;                (cases type rator-type
;                  (proc-type (var-types result-type)
;                             (begin
;                               (check-equal-type! var-types rand-types rator)
;                               result-type))
;                  (else
;                   (report-rator-not-a-proc-type rator-type rator)))))
;    (letrec-exp (p-result-type p-name b-vars b-var-types p-body letrec-body)
;                (let ((tenv-for-letrec-body
;                       (extend-tenv
;                        p-name
;                        (proc-type b-var-types p-result-type)
;                        tenv)))
;
;                  (let ((p-body-type (type-of
;                                      p-body
;                                      (extend-tenv* b-vars b-var-types tenv-for-letrec-body))))
;                    (check-equal-type! p-body-type p-result-type p-body)
;                    (type-of letrec-body tenv-for-letrec-body ))))))

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
    (proc-exp (vars var-types body)
              (proc-val (procedure vars body env)))
    (call-exp (exp args)
              (apply-procedure
               (expval->proc (value-of exp env))
               (map (lambda (arg) (value-of arg env)) args)))

    (letrec-exp (p-result-type p-name b-vars b-var-types p-body letrec-body)
                (value-of letrec-body
                          (extend-env-rec p-name b-vars p-body env)))
    (qualified-var-exp (m-name var-name)
                       (deref (lookup-qualified-var-in-env m-name var-name env)))))


;(run "module m1
;       interface
;[u : int] body
;[u = 44]
;      module m2
;       interface
;[v : int] body
;[v = -(from m1 take u,11)] -(from m1 take u, from m2 take v)")

;(run "module m1
;      interface
;      [u : int]
;      body [u = 44]
;
;      -(0, from m1 take u)
;      ")

;(run "module m1
;      interface
;     [x : int  y:int]
;      body [x = 44]
;
;      from m1 take x
;      ")

;(run "module m1
;      interface
;     [x : int]
;      body [x = 44 y = 33]
;
;      from m1 take y
;      ")

;(run "module m1
;      interface
;     [y : int]
;      body [x = 44 y = -(0,x)]
;
;      from m1 take y
;      ")