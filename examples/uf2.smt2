
; simple QF_UF test
; (set-logic QF_UF)

; expect: unsat

(declare-sort i 0)
(declare-fun a () i)
(declare-fun b () i)
(declare-fun c () i)
(declare-fun f (i) i)

(assert (= (f a) b))
(assert (= (f b) c))
(assert (= (f c) a))
(assert (not (= (f (f (f a))) a)))

(check-sat)
