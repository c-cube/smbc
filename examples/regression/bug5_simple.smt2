; expect: sat

(declare-sort i 0)
(declare-fun a () i)
(declare-fun b () i)
(assert (not (= a b)))
(check-sat)


