#lang eopl


(define (end-cont)
  (lambda (val)
    (begin
      (eopl:printf "End of computation.~%")
      (eopl:printf "This sentence should appear only once.~%")
      val)))


(define (apply-cont val cont)
  (cont val))

; remove-first


(define (remove-first  s los)
  (remove-first/k s los (end-cont)))

(define (remove-first/k s los cont)
  (cond
    ((null? los) (cont `()))
    ((eqv? s (car los)) (apply-cont (cdr los) cont))
    (else
     (remove-first/k s (cdr los) (lambda (rest)
                                   (apply-cont (cons (car los) rest) cont))))))



; list-sum

(define (list-sum los)
  (list-sum/k los (end-cont)))

(define (list-sum/k los cont)
  (if (eqv? (length los) 1)
      (apply-cont (car los) cont)
      (list-sum/k (cdr los) (lambda (val)
                              (apply-cont (+ val (car los)) cont)))))


; occurs-free?

(define (occurs-free? var exp1)
  (occurs-free?/k var exp1 (end-cont)))

(define (occurs-free?/k var exp cont)
  (cond
    ((symbol? exp) (apply-cont (eqv? var exp) cont))
    ((eqv? (car exp) 'lambda)
     (if (eqv? var (car (cadr exp)))
         (apply-cont (not (eqv? var (car (cadr exp)))) cont)
         (occurs-free?/k var (caddr exp) (lambda (val)
                                           (apply-cont val cont)))))
    (else
     (occurs-free?/k var (car exp) (lambda (val1)
                                     (if val1
                                         (apply-cont val1 cont)
                                         (occurs-free?/k var (cadr exp) (lambda (val2)
                                                                          (apply-cont val2 cont)))))))))
; (occurs-free? 'x 'x) #t
; (occurs-free? 'x 'y) #f
; (occurs-free? 'x '(lambda (x) (x y))) #f
; (occurs-free? 'x '(lambda (y) (x y))) #t
; (occurs-free? 'x '((lambda (x) x) (x y))) #t
; (occurs-free? 'x '(lambda (y) (lambda (z) (x (y z))))) #t



; subst

(define (subst new old slist)
  (subst/k new old slist (end-cont)))

(define subst/k
  (lambda (new old slist cont)
    (if (null? slist)
        (apply-cont '() cont)
        (subst-in-s-exp/k new old (car slist) (lambda (val1)
                                                (subst/k new old (cdr slist) (lambda (val2)
                                                         (apply-cont (cons val1 val2) cont))))))))


(define subst-in-s-exp/k
  (lambda (new old sexp cont)
    (if (symbol? sexp)
        (if (eqv? sexp old) (apply-cont new cont) (apply-cont sexp cont))
        (subst/k new old sexp cont))))
