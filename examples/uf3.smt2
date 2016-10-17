
; simple QF_UF test
; (set-logic QF_UF)

; expect: unsat

(declare-sort i 0)
(declare-fun a () i)
(declare-fun b () i)
(declare-fun c () i)
(declare-fun f (i) i)
(declare-fun p (i) Bool)

(assert (= (f a) b))
(assert (= (f b) c))
(assert (= (f c) a))
(assert (not (p c)))
(assert (or (p a) (p (f b))))

(check-sat)
