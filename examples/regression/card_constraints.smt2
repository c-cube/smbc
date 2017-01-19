; expect: UNSAT

; two cardinality constraints that express that `i` has at most 2
; elements, and at least 3 elements

(declare-sort i 0)

; max card: 2
(declare-fun a () i)
(declare-fun b () i)
(assert (forall ((x i)) (or (= x a) (= x b))))

(declare-fun i2 () i)
(declare-fun i1 () i)
(declare-fun i3 () i)

; min card: 3
(assert (and (not (= i1 i2)) (not (= i2 i3)) (not (= i1 i3))))

(check-sat)

