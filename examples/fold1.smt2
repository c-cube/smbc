
; expect: SAT

; distinguish between lists of natural numbers using only `fold`
; the solver must synthesize a function and an initial accumulator

; this time it's about distinguishing lists by the modulo 3 of their sum

(declare-datatypes () ((nat (s (select_s_0 nat))
                            (z))))

(declare-datatypes
   ()
   ((list (cons (select_cons_0 nat) (select_cons_1 list)) (nil))))

(define-funs-rec
   ((plus ((x nat) (y nat)) nat))
   ((match x (case (s x2) (s (plus x2 y)))
             (case z y))))

(define-funs-rec
   ((sum ((l_2 list)) nat))
   ((match l_2 (case (cons x_6 tail_2) (plus x_6 (sum tail_2)))
               (case nil z))))

(define-fun-rec
  modulo3 ((x nat)) nat
   (match x
     (case z z)
     (case (s x1)
       (match x1 (case z (s z))
         (case (s x2)
           (match x2 (case z (s (s z)))
             (case (s x3) (modulo3 x3))))))))

(declare-sort acc 0)
(declare-fun acc_init () acc)
(declare-fun f (acc nat) acc)

; force card(acc) to be 3
(declare-fun a0 () acc)
(declare-fun a1 () acc)
(declare-fun a2 () acc)

(assert (not (= a0 a1)))
(assert (not (= a0 a2)))
(assert (not (= a1 a2)))
(assert (forall ((x acc)) (or (= x a0) (= x a1) (= x a2))))

; injective function acc->nat
(declare-fun acc_to_nat (acc) nat)
(assert (not (= (acc_to_nat a0) (acc_to_nat a1))))
(assert (not (= (acc_to_nat a0) (acc_to_nat a2))))
(assert (not (= (acc_to_nat a1) (acc_to_nat a2))))

(define-fun-rec
  fold
    ((a acc) (l list)) acc
    (match l
      (case nil a)
      (case (cons x tail)
        (let ((a2 (f a x)))
          (fold a2 tail)))))

(define-fun n0 () nat z)
(define-fun n1 () nat (s n0))
(define-fun n2 () nat (s n1))
(define-fun n3 () nat (s n2))
(define-fun n4 () nat (s n3))
(define-fun n5 () nat (s n4))
(define-fun n6 () nat (s n5))
(define-fun n7 () nat (s n6))

(define-fun l0 () list (cons n0 (cons n1 (cons n2 (cons n3 nil)))))
(define-fun l1 () list (cons n1 (cons n2 (cons n3 (cons n4 nil)))))
(define-fun l2 () list (cons n0 (cons n1 (cons n2 (cons n3 (cons n4 (cons n5 nil)))))))
(define-fun l3 () list (cons n1 (cons n3 (cons n4 (cons n5 (cons n6 (cons n7 nil)))))))

(assert-not
 (not
   (and
    (= (acc_to_nat (fold acc_init l0)) (modulo3 (sum l0)))
    (= (acc_to_nat (fold acc_init l1)) (modulo3 (sum l1)))
    (= (acc_to_nat (fold acc_init l2)) (modulo3 (sum l2)))
    (= (acc_to_nat (fold acc_init l3)) (modulo3 (sum l3)))
    (not (= (fold acc_init l0) (fold acc_init l1)))
    (not (= (fold acc_init l2) (fold acc_init l3)))
    (not (= (modulo3 (sum l0)) (modulo3 (sum l1)))) ; safety check
    (not (= (modulo3 (sum l2)) (modulo3 (sum l3)))) ; safety check
   )))

(check-sat)
