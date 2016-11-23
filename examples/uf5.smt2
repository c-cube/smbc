

; simple QF_UF test
; (set-logic QF_UF)

; expect: SAT

(declare-sort i 0)
(declare-fun a () i)
(declare-fun b () i)
(declare-fun c () i)
(declare-fun f (i) i)
(declare-fun p (i) Bool)
(declare-fun test () Bool)

(assert (= (f a) b))
(assert (= (f b) c))
(assert (= (f c) a))
(assert (not (p (f c))))
(assert (p (ite test a (f (f (f b))))))

(check-sat)
