
; simple QF_UF test
; (set-logic QF_UF)

; expect: unsat

(declare-sort i 0)
(declare-fun a () i)
(declare-fun b () i)
(declare-fun f (i) i)

(assert (= a b))
(assert (not (= (f a) (f b))))

(check-sat)
