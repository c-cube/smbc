
; uninterpreted functions
; expect: SAT
(declare-sort u 0)
(declare-fun a () u)
(declare-fun b () u)
(declare-fun f_8 (u) Bool)
(assert (not (= (f_8 a) (f_8 b))))
; u = {a,b}
(assert (forall ((x_45 u)) (or (= x_45 a) (= x_45 b))))
(assert-not (forall ((x_46 u)) (not (not (= (f_8 x_46) (f_8 b))))))(check-sat)
