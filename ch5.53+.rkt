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
    (expression ("*" "(" expression "," expression ")") mul-exp)
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
    (expression ("signal" "(" expression ")") signal-exp)
    (expression ("yield" "(" ")") yield-exp)
    (expression ("kill" "(" expression ")") kill-exp)
    (expression ("receive" "(" expression ")") receive-exp)
    (expression ("send" "(" expression "," expression ")") send-exp)))

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
                 ((job->proc first-ready-thread))))))

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

(define-datatype msg msg?
  (a-msg
   (receiver-id expval?)
   (sender-id expval?)
   (my-job job?)))

(define (msg->job m)
  (cases msg m
    (a-msg (receiver-id sender-id my-job) my-job)
    (else (eopl:error 'msg->job "msg->job ~s." m))))

(define (msg->receiver-id m)
  (cases msg m
    (a-msg (receiver-id sender-id my-job) receiver-id)
    (else (eopl:error 'msg->job "msg->job ~s." m))))

(define (msg->sender-id m)
  (cases msg m
    (a-msg (receiver-id sender-id my-job) sender-id)
    (else (eopl:error 'msg->job "msg->job ~s." m))))

(define the-msg-queue `())

(define (place-on-msg-queue! th)
  (set! the-msg-queue
        (enqueue the-msg-queue th)))

(define (eat-msg receiver-id sender-id data)
  (find-and-eat-msg! receiver-id sender-id (lambda (cur-msg)
                                   (if (null? cur-msg)
                                       empty
                                       (place-on-ready-queue! (a-job
                                                               (msg->receiver-id cur-msg)
                                                               (lambda () ((job->proc (msg->job cur-msg)) data))))))))

(define (find-and-eat-msg! receiver-id sender-id fn)
  (letrec ((cur-msg `()) (loop (lambda (queue0)
                                 (cond
                                   ((null? queue0) `())
                                   ((= (expval->num receiver-id) (expval->num (msg->receiver-id (car queue0))))
                                    (if (= (expval->num (msg->sender-id (car queue0))) (expval->num sender-id))
                                        (begin
                                          (set! cur-msg (car queue0))
                                          (cdr queue0))
                                        empty))
                                   (cons (car queue0) (loop (cdr queue0)))))))
    (set! the-msg-queue (loop the-msg-queue))
    (fn cur-msg)))

(define get-fresh-id 
  (let ((inner-id 0))
    (lambda ()
      (set! inner-id (+ inner-id 1))
      (num-val inner-id))))

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

(define (cont->th-id cont)
  (cases continuation cont
    (end-cont (th-id) th-id)
    (zero1-cont (cont th-id) th-id)
    (let-exp-cont (vars exps body binding-eval-env body-eval-env cont th-id) th-id)
    (if-test-cont (exp2 exp3 env cont th-id) th-id)
    (diff1-cont (exp2 env cont th-id) th-id)
    (diff2-cont (val1 cont th-id) th-id)
    (mul1-cont (exp2 env cont th-id) th-id)
    (mul2-cont (val1 cont th-id) th-id)
    (rator-cont (rands env cont th-id) th-id)
    (rands-cont (rator rands rand-vals env cont th-id) th-id)
    (pair-car-cont (exp2 env cont th-id) th-id)
    (pair-cdr-cont (car-val cont th-id) th-id)
    (get-pair-car-cont (cont th-id) th-id)
    (get-pair-cdr-cont (cont th-id) th-id)
    (null?-cont (cont th-id) th-id)
    (list-exp-cont (vals exps env cont th-id) th-id)
    (set-rhs-cont (var env cont th-id) th-id)
    (begin-exp-cont (vals exps env cont th-id) th-id)
    (spawn-cont (cont th-id) th-id)
    (end-main-thread-cont (th-id) th-id)
    (end-subthread-cont (th-id) th-id)
    (log-cont (cont th-id) th-id)
    (wait-cont (cont th-id) th-id)
    (signal-cont (cont th-id) th-id)
    (kill-cont (cont th-id) th-id)
    (receive-cont (cont th-id) th-id)
    (send-cont1 (exp2 env cont th-id) th-id)
    (send-cont2 (receiver-id cont th-id) th-id)))

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

(define (find-and-remove! th-id queue fn)
  (letrec ((has-found #f) (cur-item empty) (loop (lambda (queue0)
                                                   (cond
                                                     ((null? queue0) `())
                                                     ((= (expval->num th-id) (expval->num (job->th-id (car queue0))))
                                                      (set! has-found #t)
                                                      (set! cur-item (car queue0))
                                                      (cdr queue0))
                                                     (else (cons (car queue0) (loop (cdr queue0))))))))
    (let ((new-queue (loop queue)))
      (fn  has-found cur-item new-queue))))

; 这个 kill 的功能目前没有实现 kill 掉 mutex 里的任务, 因为我觉得实现起来和处理 the-ready-queue 里面的差不多, 就懒得实现了.
(define (kill-thread saved-cont cur-th-id my-th-id)
  (find-and-remove! cur-th-id the-ready-queue (lambda (has-found item new-queue)
                                                ; 自己 kill 掉自己的时候, has-found 为 #f
                                                (if has-found
                                                    (begin
                                                      (set! the-ready-queue new-queue)
                                                      (apply-cont saved-cont (num-val 1)))
                                                    (if (= (expval->num cur-th-id) (expval->num my-th-id))
                                                        (run-next-thread)
                                                        (apply-cont saved-cont (num-val 0)))))))

(define-datatype job job?
  (a-job
   (th-id expval?)
   (proc procedure?)))

(define (job->th-id j)
  (cases job j
    (a-job (th-id proc) th-id)
    (else (eopl:error 'job->th-id "job->th-id ~s." j))))

(define (job->proc j)
  (cases job j
    (a-job (th-id proc) proc)
    (else (eopl:error 'job->th-id "job->th-id ~s." j))))

(define-datatype continuation continuation?
  (end-cont
   (th-id expval?))
  (zero1-cont
   (cont continuation?)
   (th-id expval?))
  (let-exp-cont
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?)
   (binding-eval-env environment?)
   (body-eval-env environment?)
   (cont continuation?)
   (th-id expval?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (diff1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (diff2-cont
   (val1 expval?)
   (cont continuation?)
   (th-id expval?))
  (mul1-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (mul2-cont
   (val1 expval?)
   (cont continuation?)
   (th-id expval?))
  (rator-cont
   (rands (list-of expression?))
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (rands-cont
   (rator expval?)
   (rands (list-of expression?))
   (rand-vals (list-of expval?))
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (pair-car-cont
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (pair-cdr-cont
   (car-val expval?)
   (cont continuation?)
   (th-id expval?))
  (get-pair-car-cont
   (cont continuation?)
   (th-id expval?))
  (get-pair-cdr-cont
   (cont continuation?)
   (th-id expval?))
  (null?-cont
   (cont continuation?)
   (th-id expval?))
  (list-exp-cont
   (vals (list-of expval?))
   (exps (list-of expression?))
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (set-rhs-cont
   (var identifier?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (begin-exp-cont
    (vals (list-of expval?))
    (exps (list-of expression?))
    (env environment?)
    (cont continuation?)
    (th-id expval?))
  (spawn-cont
   (cont continuation?)
   (th-id expval?))
  (end-main-thread-cont
   (th-id expval?))
  (end-subthread-cont
   (th-id expval?))
  (log-cont
   (cont continuation?)
   (th-id expval?))
  (wait-cont
   (cont continuation?)
   (th-id expval?))
  (signal-cont
   (cont continuation?)
   (th-id expval?))
  (kill-cont
   (cont continuation?)
   (th-id expval?))
  (receive-cont
   (cont continuation?)
   (th-id expval?))
  (send-cont1
   (exp2 expression?)
   (env environment?)
   (cont continuation?)
   (th-id expval?))
  (send-cont2
   (receiver-id expval?)
   (cont continuation?)
   (th-id expval?)))

(define (apply-cont cont val)
  (if (time-expired?)
      (begin
        (place-on-ready-queue!
         (a-job
          (cont->th-id cont)
          (lambda () (apply-cont cont val))))
        (run-next-thread))
      (begin
        (decrement-timer!)
        (cases continuation cont
          (end-cont (th-id)
                    (begin
                      (eopl:printf "End of computation.~%")
                      val))
          (zero1-cont (saved-cont th-id)
                      (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
          (let-exp-cont (vars exps body binding-eval-env body-eval-env saved-cont th-id)
                        (let ((my-env (extend-env (car vars) (newref val) body-eval-env)))
                          (if (= (length vars) 1)
                              (value-of/k body my-env saved-cont)
                              (value-of/k (car exps) binding-eval-env
                                          (let-exp-cont (cdr vars) (cdr exps) body binding-eval-env my-env saved-cont th-id)))))
          (if-test-cont (exp2 exp3 saved-env saved-cont th-id)
                        (if (expval->bool val)
                            (value-of/k exp2 saved-env saved-cont)
                            (value-of/k exp3 saved-env saved-cont)))
          (diff1-cont (exp2 saved-env saved-cont th-id)
                      (value-of/k exp2 saved-env (diff2-cont val saved-cont th-id)))
          (diff2-cont (val1 saved-cont th-id)
                      (let ((num1 (expval->num val1))
                            (num2 (expval->num val)))
                        (apply-cont saved-cont (num-val (- num1 num2)))))
          (mul1-cont (exp2 saved-env saved-cont th-id)
                     (value-of/k exp2 saved-env (mul2-cont val saved-cont th-id)))
          (mul2-cont (val1 saved-cont th-id)
                     (let ((num1 (expval->num val1))
                           (num2 (expval->num val)))
                       (apply-cont saved-cont (num-val (* num1 num2)))))
          (rator-cont (rands saved-env saved-cont th-id)
                      (value-of/k (car rands) saved-env
                                  (rands-cont val (cdr rands) `() saved-env saved-cont th-id)))
          (rands-cont (rator rands rand-vals saved-env saved-cont th-id)
                      (if (null? rands)
                          (let ((proc1 (expval->proc rator)))
                            (apply-procedure/k proc1 (append rand-vals (list val)) saved-cont))
                          (value-of/k (car rands) saved-env
                                      (rands-cont rator (cdr rands) (append rand-vals (list val)) saved-env saved-cont th-id))))
          (pair-car-cont (exp2 saved-env saved-cont th-id)
                         (value-of/k exp2 saved-env
                                     (pair-cdr-cont val saved-cont th-id)))
          (pair-cdr-cont (car-val saved-cont th-id)
                         (apply-cont saved-cont
                                     (pair-val car-val val)))
          (get-pair-car-cont (saved-cont th-id)
                             (apply-cont saved-cont (get-pair-car val)))
          (get-pair-cdr-cont (saved-cont th-id)
                             (apply-cont saved-cont (get-pair-cdr val)))
          (null?-cont (saved-cont th-id)
                      (apply-cont saved-cont (is-null? val)))
          (list-exp-cont (vals exps saved-env saved-cont th-id)
                         (let ((new-vals (append vals (list val))))
                           (if (null? exps)
                               (apply-cont saved-cont (list->pairs new-vals))
                               (value-of/k (car exps) saved-env
                                           (list-exp-cont new-vals
                                                          (cdr exps)
                                                          saved-env
                                                          saved-cont
                                                          th-id)))))
          (set-rhs-cont (var saved-env saved-cont th-id)
                        (begin
                          (setref! (apply-env saved-env var)
                                   val)
                          (apply-cont saved-cont (num-val 1))))
          (begin-exp-cont (vals exps saved-env saved-cont th-id)
                          (let ((new-vals (append vals (list val))))
                            (if (null? exps)
                                (apply-cont saved-cont val)
                                (value-of/k (car exps) saved-env
                                            (begin-exp-cont new-vals
                                                            (cdr exps)
                                                            saved-env
                                                            saved-cont
                                                            th-id)))))
          (spawn-cont (saved-cont th-id)
                      (let ((proc1 (expval->proc val))
                            (new-id (get-fresh-id)))
                        (place-on-ready-queue!
                         (a-job
                          th-id
                          (lambda ()
                            (apply-procedure/k proc1
                                               (list new-id)
                                               (end-subthread-cont new-id)))))
                        (apply-cont saved-cont new-id)))
          (end-main-thread-cont (th-id)
                                (set-final-answer! val)
                                (run-next-thread))
          (end-subthread-cont (th-id)
                              (run-next-thread))
          (log-cont (saved-cont th-id)
                    (display "[log info]  ")(display val)(newline)
                    (apply-cont saved-cont (num-val 1)))
          (wait-cont (saved-cont th-id)
                     (wait-for-mutex
                      (expval->mutex val)
                      (lambda ()
                        (apply-cont saved-cont (num-val 52)))))
          (signal-cont (saved-cont th-id)
                       (signal-mutex
                        (expval->mutex val)
                        (lambda () (apply-cont saved-cont (num-val 53)))))
          (kill-cont (saved-cont th-id)
                     (kill-thread saved-cont val th-id))
          (receive-cont (saved-cont th-id)
                        (place-on-msg-queue!
                         (a-msg
                          th-id
                          val
                          (a-job
                           th-id
                           (lambda (d)
                             (apply-cont saved-cont d)))))
                        (run-next-thread))
          (send-cont1 (exp2 saved-env saved-cont th-id)
                      (value-of/k exp2 saved-env
                                  (send-cont2 val saved-cont th-id)))
          (send-cont2 (receiver-id saved-cont th-id)
                      (eat-msg receiver-id th-id val)
                      (apply-cont saved-cont (num-val 1)))))))



(define (run string)
  (value-of-program 3 (scan&parse string)))

(define (value-of-program timeslice pgm)
  (init-store)
  (init-scheduler timeslice)
  (cases program pgm
    (a-program (exp1) (value-of/k exp1 (init-env) (end-main-thread-cont (get-fresh-id))))))

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
               (value-of/k exp1 env (zero1-cont cont (cont->th-id cont))))
    (if-exp (exp1 exp2 exp3)
            (value-of/k exp1 env (if-test-cont exp2 exp3 env cont (cont->th-id cont))))
    (let-exp (vars exps body)
             (value-of/k (car exps) env (let-exp-cont vars (cdr exps) body env env cont (cont->th-id cont))))
    (diff-exp (exp1 exp2)
              (value-of/k exp1 env (diff1-cont exp2 env cont (cont->th-id cont))))
    (mul-exp (exp1 exp2)
             (value-of/k exp1 env (mul1-cont exp2 env cont (cont->th-id cont))))
    (call-exp (rator rands)
              (value-of/k rator env
                          (rator-cont rands env cont (cont->th-id cont))))
    (cons-exp (exp1 exp2)
              (value-of/k exp1 env
                          (pair-car-cont exp2 env cont (cont->th-id cont))))
    (emptylist-exp ()
                   (apply-cont cont (emptypair-val)))
    (car-exp (exp1)
             (value-of/k exp1 env
                         (get-pair-car-cont cont (cont->th-id cont))))
    (cdr-exp (exp1)
             (value-of/k exp1 env
                         (get-pair-cdr-cont cont (cont->th-id cont))))
    (null?-exp (exp1)
               (value-of/k exp1 env
                           (null?-cont cont (cont->th-id cont))))
    (list-exp (exps)
              (value-of/k (car exps) env
                          (list-exp-cont (list) (cdr exps) env cont (cont->th-id cont))))
    (assign-exp (var exp1)
                (value-of/k exp1 env
                            (set-rhs-cont var env cont (cont->th-id cont))))
    (begin-exp (exps)
               (value-of/k (car exps) env
                           (begin-exp-cont (list) (cdr exps) env cont (cont->th-id cont))))
    (spawn-exp (exp1)
               (value-of/k exp1 env
                           (spawn-cont cont (cont->th-id cont))))
    (log-exp (exp1)
             (value-of/k exp1 env
                         (log-cont cont (cont->th-id cont))))
    (mutex-exp ()
               (apply-cont cont (mutex-val (new-mutex))))
    (wait-exp (exp1)
              (value-of/k exp1 env
                          (wait-cont cont (cont->th-id cont))))
    (signal-exp (exp1)
                (value-of/k exp1 env
                            (signal-cont cont (cont->th-id cont))))
    (yield-exp ()
               (let ((time-slice the-time-remaining))
                 (place-on-ready-queue!
                  (a-job
                   (cont->th-id cont)
                   (lambda ()
                     (set! the-time-remaining time-slice)
                     (apply-cont cont (num-val 99))))))
               (run-next-thread))
    (kill-exp (exp1)
              (value-of/k exp1 env
                          (kill-cont cont (cont->th-id cont))))
    (send-exp (exp1 exp2)
              (value-of/k exp1 env
                          (send-cont1 exp2 env cont (cont->th-id cont))))
    (receive-exp (exp1)
                 (value-of/k exp1 env
                             (receive-cont cont (cont->th-id cont))))))


(run "let fn1 = proc(dummy) begin print(100); send(2, 1024); print(-100) end in let fn2 = proc(dummy) begin print(200); let msg = receive(3) in print(msg) ; print(-200) end
in begin spawn(fn2); spawn(fn1); print(88) end")