
; expect: SAT

(declare-datatypes () ((Nat (Zero) (Succ (Prec Nat)))))
(declare-datatypes () ((List (Nil) (Cons (Head Nat)(Tail List)))))

(define-fun-rec eq-nat ((a Nat) (b Nat)) Bool
  (match a
    (case Zero
      (match b
       (case Zero true)
       (case (Succ b2) false)))
    (case (Succ a2)
      (match b
       (case Zero false)
       (case (Succ b2) (eq-nat a2 b2))))))

(define-fun-rec eq-list ((a List) (b List)) Bool
  (match a
    (case Nil
      (match b
       (case Nil true)
       (case (Cons b2 b3) false)))
    (case (Cons a2 a3)
      (match b
       (case Nil false)
       (case (Cons b2 b3) (and (eq-nat a2 b2) (eq-list a3 b3)))))))

(assert-not
  (forall ((a Nat)(b Nat))
   (eq-list (Cons a (Cons b Nil)) (Cons b (Cons a Nil)))))
