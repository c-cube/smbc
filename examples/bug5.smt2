; expect: sat

(declare-sort i 0)
(declare-fun i2 () i)
(declare-fun i1 () i)
(declare-fun i3 () i)
(assert (and (not (= i1 i2)) (not (= i2 i3)) (not (= i1 i3))))
(check-sat)


