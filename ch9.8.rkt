#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-identifier (letter (arbno (or digit letter "-"))) symbol)))

(define the-grammar
  '((program ((arbno class-decl) expression) a-program)
    (class-decl ("class" my-identifier "extends" my-identifier (arbno "field" my-identifier) (arbno method-decl)) a-class-decl)
    (method-decl ("method" my-identifier "(" (separated-list my-identifier ",")  ")" expression) a-method-decl)
    (expression ("new" my-identifier "(" (separated-list expression ",") ")") new-object-exp)
    (expression ("send" expression my-identifier "(" (separated-list expression ",") ")") method-call-exp)
    (expression ("super" my-identifier "(" (separated-list my-identifier ",") ")") super-call-exp)
    (expression ("self") self-exp)
    (expression (my-number) const-exp)
    (expression (my-identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno my-identifier "=" expression) "in" expression) let-exp)
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
    (expression ("let*" (arbno my-identifier "=" expression) "in" expression) let*-exp)
    (expression ("proc" "(" (separated-list my-identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letproc" my-identifier "=" "(" my-identifier ")" expression "in" expression) let-proc-exp)
    (expression ("letrec" (arbno my-identifier "(" (separated-list my-identifier ",") ")" "=" expression) "in" expression) let-rec-exp)
    (expression ("set" my-identifier "=" expression) assign-exp)
    (expression ("log" "(" expression ")") log-exp)
    (expression ("begin" (separated-list expression ";") "end") begin-exp)
    (expression
     ("instanceof" "(" expression "," my-identifier ")")
     inst-of-exp)
    (expression
     ("fieldref" expression my-identifier)
     fieldref-exp)
    (expression
     ("fieldset" expression my-identifier "=" expression )
     fieldset-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define identifier? symbol?)

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

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

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))

(define (init-env)
  (extend-env
   'i (newref (num-val 10))
   (extend-env
    'v (newref (num-val 50))
    (extend-env
     'x (newref (num-val 100)) (empty-env)))))


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

(define-datatype object object?
  (an-object
   (class-name identifier?)
   (fields (list-of reference?))))

(define (object->fields obj)
  (cases object obj
    (an-object (class-name fields) fields)))

(define (object->class-name obj)
  (cases object obj
    (an-object (class-name fields) class-name)))

(define (new-object class-name)
  (an-object
   class-name
   (map
    (lambda (field-name)
      (newref (list 'undefined field-name)))
    (class->field-names (lookup-class class-name)))))

(define-datatype method method?
  (a-method
   (vars (list-of identifier?))
   (body expression?)
   (super-name identifier?)
   (field-names (list-of identifier?))))

(define (apply-method m self args)
  (cases method m
    (a-method (vars body super-name field-names)
              (value-of body
                        (extend-env* vars (map newref args)
                                     (extend-env-with-self-and-super
                                      self
                                      super-name
                                      (extend-env*  field-names
                                                    (object->fields self)
                                                    (empty-env))))))))

(define (extend-env-with-self-and-super self super-name env)
  (extend-env '%self (newref self)
              (extend-env '%super (newref super-name) env)))
  

(define the-class-env `())

(define (add-to-class-env! class-name class)
  (set! the-class-env
        (cons
         (list class-name class)
         the-class-env)))

(define (lookup-class name)
  (let ((maybe-pair (assq name the-class-env)))
    (if maybe-pair
        (cadr maybe-pair)
        (eopl:error 'report-unknown-class "~s" name))))

(define-datatype class class?
  (a-class
   (super-name (maybe identifier?))
   (field-names (list-of identifier?))
   (method-env method-environment?)))

(define (method-environment? env) (list-of (list-of method-decl?)))

(define (class->field-names c)
  (cases class c
    (a-class (super-name field-names method-env) field-names)))

(define (class->method-env c)
  (cases class c
    (a-class (super-name field-names method-env) method-env)))

(define (class->super-name c)
  (cases class c
    (a-class (super-name field-names method-env) super-name)))

(define (initialize-class-env! c-decls)
  (add-to-class-env! 'object (a-class #f '() '()))
  (for-each initialize-class-decl! c-decls))

(define (initialize-class-decl! c-decl)
  (cases class-decl c-decl
    (a-class-decl (c-name s-name f-names m-decls)
                  (let ((f-names
                         (append-field-names
                          (class->field-names (lookup-class s-name))
                          f-names)))
                    (add-to-class-env!
                     c-name
                     (a-class s-name f-names
                              (merge-method-envs
                               (class->method-env (lookup-class s-name))
                               (method-decls->method-env
                                m-decls s-name f-names))))))))

(define (append-field-names super-fields new-fields)
  (cond
    ((null? super-fields) new-fields)
    (else
     (cons
      (if (memq (car super-fields) new-fields)
          (fresh-identifier (car super-fields))
          (car super-fields))
      (append-field-names
       (cdr super-fields)
       new-fields)))))

(define (find-method c-name name)
  (let ((m-env (class->method-env (lookup-class c-name))))
    (let ((maybe-pair (assq name m-env)))
      (if (pair? maybe-pair)
          (cadr maybe-pair)
          (eopl:error `report-method-not-found "~s" name)))))

(define (method-decls->method-env m-decls super-name field-names)
  (map
   (lambda (m-decl)
     (cases method-decl m-decl
       (a-method-decl (method-name vars body)
                      (list method-name
                            (a-method vars body super-name field-names)))))
   m-decls))

(define (merge-method-envs super-m-env new-m-env)
  (append new-m-env super-m-env))



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

(define (is-instance-of name1 name2)
  (if (eqv? name1 name2)
      #t
      (let ((name3 (class->super-name (lookup-class name1))))
        (if name3
            (is-instance-of name3 name2)
            #f))))

(define (run string)
  (value-of-program (scan&parse string)))

(define (value-of-program pgm)
  (initialize-store!)
  (cases program pgm
    (a-program (class-decls body)
               (initialize-class-env! class-decls)
               (value-of body (init-env)))))

(define (values-of-exps exps env)
  (map (lambda (exp)
         (value-of exp env))
       exps))

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
    (let*-exp (vars exps body)
              (let*-val vars exps body env))
    (proc-exp (vars body)
              (proc-val (procedure vars body env)))
    (call-exp (exp args)
              (apply-procedure
               (expval->proc (value-of exp env))
               (map (lambda (arg) (value-of arg env)) args)))
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
               (begin-val exps env))
    (log-exp (exp1)
             (let ((val (value-of exp1 env)))
               (display "[log info]  ")(display val)(newline)))
    (self-exp ()
              (deref (apply-env env '%self)))
    (method-call-exp (obj-exp method-name rands)
                     (let ((args (values-of-exps rands env))
                           (obj (value-of obj-exp env)))
                       (apply-method
                        (find-method
                         (object->class-name obj)
                         method-name)
                        obj
                        args)))
    (super-call-exp (method-name rands)
                    (let ((args (values-of-exps rands env))
                          (obj (deref (apply-env env '%self))))
                      (apply-method
                       (find-method
                        (deref (apply-env env '%super))
                        method-name)
                       obj
                       args)))
    (new-object-exp (class-name rands)
                    (let ((args (values-of-exps rands env))
                          (obj (new-object class-name)))
                      (apply-method
                       (find-method
                        class-name
                        'initialize)
                       obj
                       args)
                      obj))
    (inst-of-exp (exp1 name)
                 (let ((c-name (object->class-name (value-of exp1 env))))
                   (is-instance-of c-name name)))
    (fieldref-exp (exp1 field-name)
                  (let* ((obj (value-of exp1 env))
                         (c-name (object->class-name obj))
                         (fields (class->field-names (lookup-class c-name)))
                         (idx (element-index field-name fields)))
                    (if idx
                        (deref (list-ref (object->fields obj) idx))
                        (eopl:error 'fieldref-exp "not found field ~s." field-name))))
    (fieldset-exp (exp1 field-name exp2)
                  (let* ((obj (value-of exp1 env))
                         (c-name (object->class-name obj))
                         (fields (class->field-names (lookup-class c-name)))
                         (idx (element-index field-name fields)))
                    (if idx
                        (setref! (list-ref (object->fields obj) idx) (value-of exp2 env))
                        (eopl:error 'fieldref-exp "not found field ~s." field-name))))))

(define element-index
  (letrec
      ([element-index-helper
        (lambda (e lst index)
          (cond [(null? lst) #f]
                [(eqv? e (car lst)) index]
                [else (element-index-helper e (cdr lst) (+ index 1))]))])
    (lambda (e lst)
      (element-index-helper e lst 0))))



(run "


class c1 extends object
field c11
field c12
method initialize () begin set c11 = 11; set c12 = 12 end
method m1 () 11
method m2 () send self m1()

class c2 extends c1
field c21
field c12
method initialize () begin super initialize(); set c21 = 21; set c12 = 120 end

class c3 extends object
method initialize () 3

let o2 = new c2() in begin log(fieldref o2 c21); log(fieldref o2 c12); log(fieldref o2 c11); fieldset o2 c11 = 101; log(fieldref o2 c11) end

")