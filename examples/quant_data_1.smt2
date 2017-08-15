
; all factorials are smaller than 100
; expect: unsat

(declare-datatypes () ((nat (s (select_s_0 nat)) 
                            (z))))
(define-funs-rec
   ((plus ((x nat) (y nat)) nat))
   ((match x (case (s x2) (s (plus x2 y))) 
             (case z y))))
(define-funs-rec
   ((mult ((x_1 nat) (y_1 nat)) nat))
   ((match x_1 (case (s x2_1) (plus y_1 (mult x2_1 y_1))) 
               (case z z))))
(define-funs-rec
   ((leq ((x_2 nat) (y_2 nat)) Bool))
   ((match x_2
      (case (s x2_2) (match y_2 (case (s y2) (leq x2_2 y2)) 
                                (case z false))) 
      (case z true))))
(define-funs-rec
   ((fact ((n nat)) nat))
   ((match n (case (s n2) (mult n (fact n2))) 
             (case z (s z)))))
(define-funs-rec ((num_5 () nat)) ((s (s (s (s (s z)))))))
(define-funs-rec ((num_10 () nat)) ((mult (s (s z)) num_5)))
(define-funs-rec ((num_100 () nat)) ((mult num_10 num_10)))
(assert-not
  (not (forall ((n_1 nat)) (leq (fact n_1) (mult num_100 num_100)))))
(check-sat)
