
; expect: SAT

; distinguish between lists of booleans using only `fold`
; the solver must synthesize a function and an initial accumulator

(declare-datatypes () ((nat (s (select_s_0 nat))
                            (z))))

(declare-datatypes
   ()
   ((list (cons (select_cons_0 Bool) (select_cons_1 list)) (nil))))

(declare-sort acc 0)
(declare-fun acc_init () acc)
(declare-fun f (acc Bool) acc)

; force card(acc) to be 2
(declare-fun a0 () acc)
(declare-fun a1 () acc)

(assert (not (= a0 a1)))
(assert (forall ((x acc)) (or (= x a0) (= x a1))))

(define-fun-rec
  fold
    ((a acc) (l list)) acc
    (match l
      (case nil a)
      (case (cons x tail)
        (let ((a2 (f a x)))
          (fold a2 tail)))))


(define-fun l0 () list (cons false (cons false (cons true (cons false nil)))))
(define-fun l1 () list (cons false (cons true (cons false (cons false nil)))))
(define-fun l2 () list (cons false (cons false (cons false (cons false (cons true (cons false nil)))))))
(define-fun l3 () list (cons false (cons false (cons false (cons true (cons false (cons false nil)))))))

(assert-not
 (not
   (and
    (not (= (fold acc_init l0) (fold acc_init l1)))
    (not (= (fold acc_init l2) (fold acc_init l3)))
   )))

(check-sat)
