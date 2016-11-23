
; expect: SAT

(declare-datatypes () ((Direction (North)(South)(East)(West))))
(declare-datatypes () ((Nat (Zero) (Succ (Prec Nat)))))
(declare-datatypes () ((List (Nil) (Cons (Head Nat)(Tail List)))))

(declare-fun some_dir () Direction)

;(define-fun-rec (Plus ((a Nat) (b Nat)) Nat
;  (match a
;    (case Zero b)
;    (case (Succ a2) (Succ (Plus a2 b))))))

(assert-not
  (forall ((d Direction)(a Nat)(b Nat))
    (or
      (not (= d North))
      (= (Cons a (Cons b Nil)) (Cons b (Cons a Nil))))))
