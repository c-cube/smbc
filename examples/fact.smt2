
; find `n` where `n! >= 100 * 100`
; expect: SAT

(declare-datatypes () ((nat_1 (s_1 (select_s_1_0 nat_1)) 
                              (z_1))))
(define-funs-rec
   ((plus_1 ((x_3 nat_1) (y_3 nat_1)) nat_1))
   ((match x_3 (case (s_1 x2_3) (s_1 (plus_1 x2_3 y_3))) 
               (case z_1 y_3))))
(define-funs-rec
   ((mult_1 ((x_4 nat_1) (y_4 nat_1)) nat_1))
   ((match x_4
      (case (s_1 x2_4) (plus_1 y_4 (mult_1 x2_4 y_4))) 
      (case z_1 z_1))))
(define-funs-rec
   ((leq_1 ((x_5 nat_1) (y_5 nat_1)) Bool))
   ((match x_5
      (case (s_1 x2_5)
         (match y_5 (case (s_1 y2_1) (leq_1 x2_5 y2_1)) 
                    (case z_1 false))) 
      (case z_1 true))))
(define-funs-rec
   ((fact_1 ((n_2 nat_1)) nat_1))
   ((match n_2
      (case (s_1 n2_1) (mult_1 n_2 (fact_1 n2_1))) 
      (case z_1 (s_1 z_1)))))
(define-funs-rec ((num_5_1 () nat_1)) ((s_1 (s_1 (s_1 (s_1 (s_1 z_1)))))))
(define-funs-rec ((num_10_1 () nat_1)) ((mult_1 (s_1 (s_1 z_1)) num_5_1)))
(define-funs-rec ((num_100_1 () nat_1)) ((mult_1 num_10_1 num_10_1)))
(assert-not (forall ((n_3 nat_1)) (not (leq_1 num_100_1 (fact_1 n_3)))))(check-sat)
