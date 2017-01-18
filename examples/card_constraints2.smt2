; expect: UNSAT

; two cardinality constraints that express that `i` has at most 2
; elements, and at least 3 elements

; the difference with card_constraints.smt2 is the encoding, which here
; relies on existentials

(declare-sort i 0)

; max card: 2
(assert
 (exists
  ((x_0 i))
  (exists ((x_1 i)) (forall ((y i)) (or (= x_0 y) (= x_1 y))))))

; min card: 3
(assert
  (exists ((i1 i))
    (exists ((i2 i))
      (exists ((i3 i))
        (and (not (= i1 i2)) (not (= i2 i3)) (not (= i1 i3)))))))

(check-sat)

