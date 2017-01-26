
; find a list whose sum = 4, where `rev l = l`
; expect: SAT

(declare-datatypes () ((nat_1 (s_1 (select_s_1_0 nat_1)) 
                              (z_1))))
(define-funs-rec
   ((plus_1 ((x_9 nat_1) (y_5 nat_1)) nat_1))
   ((match x_9 (case (s_1 x2_3) (s_1 (plus_1 x2_3 y_5))) 
               (case z_1 y_5))))
(define-funs-rec
   ((mult_1 ((x_10 nat_1) (y_6 nat_1)) nat_1))
   ((match x_10
      (case (s_1 x2_4) (plus_1 y_6 (mult_1 x2_4 y_6))) 
      (case z_1 z_1))))
(define-funs-rec
   ((leq_1 ((x_11 nat_1) (y_7 nat_1)) Bool))
   ((match x_11
      (case (s_1 x2_5)
         (match y_7 (case (s_1 y2_1) (leq_1 x2_5 y2_1)) 
                    (case z_1 false))) 
      (case z_1 true))))
(declare-datatypes
   ()
   ((list_1 (cons_1 (select_cons_1_0 nat_1) (select_cons_1_1 list_1)) 
            (nil_1))))
(define-funs-rec
   ((append_1 ((x_12 list_1) (y_8 list_1)) list_1))
   ((match x_12
      (case (cons_1 n_1 tail_4) (cons_1 n_1 (append_1 tail_4 y_8))) 
      (case nil_1 y_8))))
(define-funs-rec
   ((rev_1 ((l_5 list_1)) list_1))
   ((match l_5
      (case (cons_1 x_13 xs_1) (append_1 (rev_1 xs_1) (cons_1 x_13 nil_1))) 
      (case nil_1 nil_1))))
(define-funs-rec
   ((length_1 ((l_6 list_1)) nat_1))
   ((match l_6
      (case (cons_1 x_14 tail_5) (s_1 (length_1 tail_5))) 
      (case nil_1 z_1))))
(define-funs-rec
   ((sum_1 ((l_7 list_1)) nat_1))
   ((match l_7
      (case (cons_1 x_15 tail_6) (plus_1 x_15 (sum_1 tail_6))) 
      (case nil_1 z_1))))
(define-funs-rec
   ((sorted_1 ((l_8 list_1)) Bool))
   ((match l_8
      (case (cons_1 x_16 l2_2)
         (match l2_2
           (case (cons_1 y_9 l3_1)
              (and (leq_1 x_16 y_9) (sorted_1 (cons_1 y_9 l3_1)))) 
           (case nil_1 true))) 
      (case nil_1 true))))
(define-funs-rec
   ((map_1 ((f_1 (=> nat_1 nat_1)) (l_9 list_1)) list_1))
   ((match l_9
      (case (cons_1 x_17 tail_7) (cons_1 (f_1 x_17) (map_1 f_1 tail_7))) 
      (case nil_1 nil_1))))
(assert-not
 (forall
    ((l_10 list_1))
    (not (and
          (= (sum_1 l_10) (s_1 (s_1 (s_1 (s_1 z_1))))) 
          (= (rev_1 l_10) l_10)))))(check-sat)
