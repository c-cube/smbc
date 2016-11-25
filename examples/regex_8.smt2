(declare-datatypes ()
  ((list3 (Nil3) (Cons3 (Cons_03 Bool) (Cons_13 list3)))))
(declare-datatypes () ((T (A) (B) (C))))
(declare-datatypes ()
  ((list (Nil) (Cons (Cons_0 T) (Cons_1 list)))))
(declare-datatypes ()
  ((R (Nil22)
     (Eps) (Atom (Atom_0 T)) (+2 (+_0 R) (+_1 R)) (>2 (>_0 R) (>_1 R))
     (Star (Star_0 R)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-datatypes ()
  ((list2 (Nil2) (Cons2 (Cons_02 Pair) (Cons_12 list2)))))
(define-fun-rec
  splits2
    ((x T) (y list2)) list2
    (match y
      (case Nil2 Nil2)
      (case (Cons2 z x2)
        (match z
          (case (Pair2 bs cs)
            (Cons2 (Pair2 (Cons x bs) cs) (splits2 x x2)))))))
(define-fun-rec
  splits
    ((x list)) list2
    (match x
      (case Nil (Cons2 (Pair2 Nil Nil) Nil2))
      (case (Cons y xs) (Cons2 (Pair2 Nil x) (splits2 y (splits xs))))))
(define-fun-rec
  ors
    ((x list3)) Bool
    (match x
      (case Nil3 false)
      (case (Cons3 y xs) (or y (ors xs)))))
(define-fun
  eqT
    ((x T) (y T)) Bool
    (match x
      (case A
        (match y
          (case default false)
          (case A true)))
      (case B
        (match y
          (case default false)
          (case B true)))
      (case C
        (match y
          (case default false)
          (case C true)))))
(define-fun-rec
  eps
    ((x R)) Bool
    (match x
      (case default false)
      (case Eps true)
      (case (+2 p q) (or (eps p) (eps q)))
      (case (>2 r q2) (and (eps r) (eps q2)))
      (case (Star y) true)))
(define-fun-rec
  okay
    ((x R)) Bool
    (match x
      (case default true)
      (case (+2 p q) (and (okay p) (okay q)))
      (case (>2 r q2) (and (okay r) (okay q2)))
      (case (Star p2) (and (okay p2) (not (eps p2))))))
(define-fun-rec
  step
    ((x R) (y T)) R
    (match x
      (case default Nil22)
      (case (Atom b) (ite (eqT b y) Eps Nil22))
      (case (+2 p q) (+2 (step p y) (step q y)))
      (case (>2 r q2)
        (ite
          (eps r) (+2 (>2 (step r y) q2) (step q2 y))
          (+2 (>2 (step r y) q2) Nil22)))
      (case (Star p2) (>2 (step p2 y) x))))
(define-fun-rec
  rec
    ((x R) (y list)) Bool
    (match y
      (case Nil (eps x))
      (case (Cons z xs) (rec (step x z) xs))))
(define-funs-rec
  ((reck2 ((p R) (q R) (x list2)) list3)
   (reck ((x R) (y list)) Bool))
  ((match x
     (case Nil2 Nil3)
     (case (Cons2 y z)
       (match y
         (case (Pair2 l r)
           (Cons3 (and (reck p l) (rec q r)) (reck2 p q z))))))
   (match x
     (case Nil22 false)
     (case Eps
       (match y
         (case Nil true)
         (case (Cons z x2) false)))
     (case (Atom c)
       (match y
         (case Nil false)
         (case (Cons b2 x3)
           (match x3
             (case Nil (eqT c b2))
             (case (Cons x4 x5) false)))))
     (case (+2 p q) (or (reck p y) (reck q y)))
     (case (>2 r q2) (ors (reck2 r q2 (splits y))))
     (case (Star p2)
       (match y
         (case Nil true)
         (case (Cons x6 x7) (and (not (eps p2)) (rec (>2 p2 x) y))))))))
(assert-not
  (forall ((p R) (q R) (s list))
    (= (rec (>2 p q) s) (rec (>2 q p) s))))
(check-sat)
