; expect: sat

(declare-sort i 0)
(assert (exists ((x_0 i)) (exists ((x_1 i)) (not (= x_0 x_1)))))
(assert
 (exists
    ((x_0_0 i))
    (exists
       ((x_1_0 i))
       (exists
          ((x_2 i))
          (forall ((y i)) (or (= x_0_0 y) (= x_1_0 y) (= x_2 y)))))))
(declare-fun i2 () i)
(declare-fun i1 () i)
(declare-fun i3 () i)
(assert (and (not (= i1 i2)) (not (= i2 i3)) (not (= i1 i3))))
(check-sat)
