#lang eopl



;; 1. proc (x) -(x,3)
(int -> int)

;; 2. proc (f) proc (x) -((f x), 1)

((t1 -> int) -> (t1 -> int))

;; 3. proc (x) x

(t -> t)

;; 4. proc (x) proc (y) (x y).

((t1 -> t1) -> (t1 -> t1))


;; 5. proc (x) (x 3)

((t1 -> t1) -> t1)

;; 6. proc (x) (x x)

((t1 -> t2) -> t2)


;; 7. proc (x) if x then 88 else 99

(bool -> int)

;; 8. proc (x) proc (y) if x then y else 99

(bool -> (t1 -> [t1 or num-val]))

;; 9. (proc (p) if p then 88 else 99 33)

int

;; 10. (proc (p) if p then 88 else 99 proc (z) z)

(t -> t)

;; 11. proc (f) proc (g)
;;     proc (p)
;;       proc (x) if (p (f x)) then (g 1) else -((f x),1)


;; 12. proc (x) proc(p)
;;     proc (f)
;;     if (p x) then -(x,1) else (f p)


;; 13. proc (f)
;;   let d = proc (x)
;;     proc (z) ((f (x x)) z)
;;        in proc (n) ((f (d d)) n)

(((t3 -> (t1 -> t2)) -> (t1 -> t2)) -> (t4 -> (t1 -> t2)))
