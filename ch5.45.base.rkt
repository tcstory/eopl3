#lang eopl

(define the-lexical-spec
  '((my-whitespace (whitespace) skip)
    (my-number (digit (arbno digit)) number)
    (my-number ("-" digit (arbno digit)) number)
    (my-identifier (letter (arbno (or digit letter "_"))) symbol)))

(define the-grammar
  '((program (expression) a-program)
    (expression (my-number) const-exp)
    (expression (my-identifier) var-exp)
    (expression ("proc" "(" (separated-list my-identifier ",") ")" expression) proc-exp)
    (expression ("letrec" (arbno my-identifier "(" (separated-list my-identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" (arbno my-identifier "=" expression) "in" expression) let-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("set" my-identifier "=" expression) assign-exp)
    (expression ("begin" (separated-list expression ";") "end") begin-exp)
    (expression ("spawn" "(" expression ")") spawn-exp)
    (expression ("print" "(" expression ")") log-exp)
    (expression ("mutex()") mutex-exp)
    (expression ("wait" "(" expression ")") wait-exp)
    (expression ("signal" "(" expression ")") signal-exp)))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define identifier? symbol?)

(define reference? integer?)

(define empty? null?)

(define the-store 'undefined)

(define (empty-store) `()) 

(define (init-store)
  (set! the-store (empty-store)))

(define (newref val)
  (let ((next-ref (length the-store)))
    (set! the-store (append the-store (list val)))
    next-ref))

(define (deref ref)
  (list-ref the-store ref))

(define (setref! ref val)
  (set! the-store (letrec ((loop (lambda (the-store0 ref0)
                                   (if (= ref0 0)
                                       (cons val (cdr the-store0))
                                       (cons (car the-store0) (loop (cdr the-store0) (- ref0 1)))))))
                    (loop the-store ref))))

(define (empty-queue) `())

(define the-ready-queue 'undefined)
(define the-final-answer 'undefined)
(define the-max-time-slice 'undefined)
(define the-time-remaining 'undefined)

(define (init-scheduler ticks)
  (set! the-ready-queue (empty-queue))
  (set! the-final-answer 'undefined)
  (set! the-max-time-slice ticks)
  (set! the-time-remaining the-max-time-slice))

(define (place-on-ready-queue! th)
  (set! the-ready-queue
        (enqueue the-ready-queue th)))

(define (run-next-thread)
  (if (empty? the-ready-queue)
      the-final-answer
      (dequeue the-ready-queue
               (lambda (first-ready-thread other-ready-threads)
                 (set! the-ready-queue other-ready-threads)
                 (set! the-time-remaining the-max-time-slice)
                 (first-ready-thread)))))

(define (set-final-answer! val)
  (set! the-final-answer val))

(define (time-expired?)
  (zero? the-time-remaining))

(define (decrement-timer!)
  (set! the-time-remaining (- the-time-remaining 1)))

(define (dequeue q th)
  (th (car q) (cdr q)))

(define (enqueue q th)
  (append q (list th)))

(define-datatype mutex mutex?
  (a-mutex
   (ref-to-closed? reference?)
   (ref-to-wait-queue reference?)))

(define (expval->mutex m)
  (cases expval m
    (mutex-val (val) val)
    (else (report-expval-extractor-error 'mutex m))))

(define (new-mutex)
  (a-mutex
   (newref #f)
   (newref `())))

(define (wait-for-mutex m th)
  (cases mutex m
    (a-mutex (ref-to-closed? ref-to-wait-queue)
             (cond
               ((deref ref-to-closed?)
                (setref! ref-to-wait-queue
                         (enqueue (deref ref-to-wait-queue) th))
                (run-next-thread))
               (else
                (setref! ref-to-closed? #t)
                (th))))))

(define (signal-mutex m th)
  (cases mutex m
    (a-mutex (ref-to-closed? ref-to-wait-queue)            
             (let ((closed? (deref ref-to-closed?))
                   (wait-queue (deref ref-to-wait-queue)))
               (if closed?
                   (if (empty? wait-queue)
                       (setref! ref-to-closed? #f)
                       (dequeue wait-queue
                                (lambda (first-waiting-th other-waiting-ths)
                                  (place-on-ready-queue! first-waiting-th)
                                  (setref! ref-to-wait-queue other-waiting-ths))))
                   empty)
               (th)))))

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

(define (extend-env-rec* p-names p-vars p-bodies saved-env)
  (if (null? p-names)
      saved-env
      (extend-env-rec*
       (cdr p-names)
       (cdr p-vars)
       (cdr p-bodies)
       (extend-env-rec (car p-names) (car p-vars) (car p-bodies) saved-env))))
                                       

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
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptypair-val)
  (proc-val
   (proc proc?))
  (mutex-val
   (val mutex?)))

(define-datatype proc proc?
  (procedure
   (vars (list-of identifier?))
   (body expression?)
   (saved-env environment?)))

(define (apply-procedure/k proc1 vals cont)
  (cases proc proc1
    (procedure (vars body saved-env)
               (value-of/k body
                           (extend-env* vars vals saved-env)
                           cont))))

(define (extend-env* vars vals env)
  (if (null? vars)
      env
      (extend-env* (cdr vars) (cdr vals) (extend-env (car vars) (newref (car vals)) env))))

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
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?)
   (binding-eval-env environment?)
   (body-eval-env environment?)
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
   (env environment?)
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
   (cont continuation?))
  (set-rhs-cont
   (var identifier?)
   (env environment?)
   (cont continuation?))
  (begin-exp-cont
    (vals (list-of expval?))
    (exps (list-of expression?))
    (env environment?)
    (cont continuation?))
  (spawn-cont
   (cont continuation?))
  (end-main-thread-cont)
  (end-subthread-cont)
  (log-cont
   (cont continuation?))
  (wait-cont
   (cont continuation?))
  (signal-cont
   (cont continuation?)))

(define (apply-cont cont val)
  (if (time-expired?)
      (begin
        (place-on-ready-queue!
         (lambda () (apply-cont cont val)))
        (run-next-thread))
      (begin
        (decrement-timer!)
        (cases continuation cont
          (end-cont ()
                    (begin
                      (eopl:printf "End of computation.~%")
                      val))
          (zero1-cont (saved-cont)
                      (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
          (let-exp-cont (vars exps body binding-eval-env body-eval-env saved-cont)
                        (let ((my-env (extend-env (car vars) (newref val) body-eval-env)))
                          (if (= (length vars) 1)
                              (value-of/k body my-env saved-cont)
                              (value-of/k (car exps) binding-eval-env
                                          (let-exp-cont (cdr vars) (cdr exps) body binding-eval-env my-env saved-cont)))))
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
          (rator-cont (rands saved-env saved-cont)
                      (value-of/k (car rands) saved-env
                                  (rands-cont val (cdr rands) `() saved-env saved-cont)))
          (rands-cont (rator rands rand-vals saved-env saved-cont)
                      (if (null? rands)
                          (let ((proc1 (expval->proc rator)))
                            (apply-procedure/k proc1 (append rand-vals (list val)) saved-cont))
                          (value-of/k (car rands) saved-env
                                      (rands-cont rator (cdr rands) (append rand-vals (list val)) saved-env saved-cont))))
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
                                                          saved-cont)))))
          (set-rhs-cont (var saved-env saved-cont)
                        (begin
                          (setref! (apply-env saved-env var)
                                   val)
                          (apply-cont saved-cont (num-val 1))))
          (begin-exp-cont (vals exps saved-env saved-cont)
                          (let ((new-vals (append vals (list val))))
                            (if (null? exps)
                                (apply-cont saved-cont val)
                                (value-of/k (car exps) saved-env
                                            (begin-exp-cont new-vals
                                                            (cdr exps)
                                                            saved-env
                                                            saved-cont)))))
          (spawn-cont (saved-cont)
                      (let ((proc1 (expval->proc val)))
                        (place-on-ready-queue!
                         (lambda ()
                           (apply-procedure/k proc1
                                              (list (num-val 28))
                                              (end-subthread-cont))))
                        (apply-cont saved-cont (num-val 73))))
          (end-main-thread-cont ()
                                (set-final-answer! val)
                                (run-next-thread))
          (end-subthread-cont ()
                              (run-next-thread))
          (log-cont (saved-cont)
                    (display "[log info]  ")(display val)(newline)
                    (apply-cont saved-cont (num-val 1)))
          (wait-cont (saved-cont)
                     (wait-for-mutex
                      (expval->mutex val)
                      (lambda ()
                        (apply-cont saved-cont (num-val 52)))))
          (signal-cont (saved-cont)
                       (signal-mutex
                        (expval->mutex val)
                        (lambda () (apply-cont saved-cont (num-val 53)))))))))



(define (run string)
  (value-of-program 3 (scan&parse string)))

(define (value-of-program timeslice pgm)
  (init-store)
  (init-scheduler timeslice)
  (cases program pgm
    (a-program (exp1) (value-of/k exp1 (init-env) (end-main-thread-cont)))))

(define (value-of/k exp env cont)
  (cases expression exp
    (const-exp (num) (apply-cont cont (num-val num)))
    (var-exp (var)
             (apply-cont cont (deref (apply-env env var))))
    (proc-exp (vars body)
              (apply-cont cont
                          (proc-val (procedure vars body env))))
    (letrec-exp (p-names p-varss p-bodies let-body)
                (value-of/k let-body
                            (extend-env-rec* p-names p-varss p-bodies env)
                            cont))
    (zero?-exp (exp1)
               (value-of/k exp1 env (zero1-cont cont)))
    (if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
    (let-exp (vars exps body)
             (value-of/k (car exps) env (let-exp-cont vars (cdr exps) body env env cont)))
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont)))
    (call-exp (rator rands)
              (value-of/k rator env
                          (rator-cont rands env cont)))
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
                          (list-exp-cont (list) (cdr exps) env cont)))
    (assign-exp (var exp1)
                (value-of/k exp1 env
                            (set-rhs-cont var env cont)))
    (begin-exp (exps)
               (value-of/k (car exps) env
                           (begin-exp-cont (list) (cdr exps) env cont)))
    (spawn-exp (exp1)
               (value-of/k exp1 env
                           (spawn-cont cont)))
    (log-exp (exp1)
             (value-of/k exp1 env
                         (log-cont cont)))
    (mutex-exp ()
               (apply-cont cont (mutex-val (new-mutex))))
    (wait-exp (exp1)
              (value-of/k exp1 env
                          (wait-cont cont)))
    (signal-exp (exp1)
                (value-of/k exp1 env
                            (signal-cont cont)))))

; 书上说 shared variable 是不可靠的, 其实理论上来说是这样的, 但是我的下面两端程序并没有复现 x 的值的异常的情况,
; 后面我排查了很久, 应该是这个出现的的情况在我的实现利比较极端, 很难出现

;(run
;   "let x = 0 in let incr_x = proc(id) proc(dummy) set x = -(x,-1)
;    in begin spawn((incr_x 100)) ; spawn((incr_x 200)) ; spawn((incr_x 300)) end")

;(run
;   "let x = 0 in let incr_x = proc(id) proc(dummy) set x = -(x,-1)
;    in let fn1 = (incr_x 100) fn2 = (incr_x 200) fn3 = (incr_x 300) in begin spawn(fn1) ; spawn(fn2) ; spawn(fn3) end")

; 书上最后还打印出了 105, 但是我看了一下, 这是不应该出现的情况, 暂时还搞不懂为啥会这样

;(run "
;let buffer = 0
;in let producer = proc (n)
;letrec
;wait(k) = if zero?(k)
;then set buffer = n
;else begin
;print(-(k,-200));
;(wait -(k,1))
;end
;in (wait 5)
;in let consumer = proc (d)
;letrec busywait (k) = if zero?(buffer)
;then begin
;print(-(k,-100));
;(busywait -(k,-1))
;end
;else buffer
;in (busywait 0)
;in begin
;spawn(proc (d) (producer 44));
;print(300);
;(consumer 86)
;end")


;(run "
;let x = 0
;      in let mut = mutex()
;      in let incr_x = proc (id)
;                       proc (dummy)
;                        begin
;                         wait(mut);
;                         print(id);
;                         set x = -(x,-1);
;                         print(-(0,id));
;                         signal(mut);
;                         print(-(id,-88))
;                        end
;      in begin
;          spawn((incr_x 100));
;          spawn((incr_x 200));
;          spawn((incr_x 300))
;end")