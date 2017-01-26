
; find `f` where: `map f [1,2,3] = [3,4,5], f 10=12`
; expect: SAT
(declare-datatypes () ((nat_4 (s_4 (select_s_4_0 nat_4)) 
                              (z_4))))
(define-funs-rec
   ((plus_4 ((x_36 nat_4) (y_20 nat_4)) nat_4))
   ((match x_36 (case (s_4 x2_12) (s_4 (plus_4 x2_12 y_20))) 
                (case z_4 y_20))))
(define-funs-rec
   ((mult_4 ((x_37 nat_4) (y_21 nat_4)) nat_4))
   ((match x_37
      (case (s_4 x2_13) (plus_4 y_21 (mult_4 x2_13 y_21))) 
      (case z_4 z_4))))
(define-funs-rec
   ((leq_4 ((x_38 nat_4) (y_22 nat_4)) Bool))
   ((match x_38
      (case (s_4 x2_14)
         (match y_22 (case (s_4 y2_4) (leq_4 x2_14 y2_4)) 
                     (case z_4 false))) 
      (case z_4 true))))
(declare-datatypes
   ()
   ((list_4 (cons_4 (select_cons_4_0 nat_4) (select_cons_4_1 list_4)) 
            (nil_4))))
(define-funs-rec
   ((append_4 ((x_39 list_4) (y_23 list_4)) list_4))
   ((match x_39
      (case (cons_4 n_4 tail_16) (cons_4 n_4 (append_4 tail_16 y_23))) 
      (case nil_4 y_23))))
(define-funs-rec
   ((rev_4 ((l_21 list_4)) list_4))
   ((match l_21
      (case (cons_4 x_40 xs_4) (append_4 (rev_4 xs_4) (cons_4 x_40 nil_4))) 
      (case nil_4 nil_4))))
(define-funs-rec
   ((length_4 ((l_22 list_4)) nat_4))
   ((match l_22
      (case (cons_4 x_41 tail_17) (s_4 (length_4 tail_17))) 
      (case nil_4 z_4))))
(define-funs-rec
   ((sum_4 ((l_23 list_4)) nat_4))
   ((match l_23
      (case (cons_4 x_42 tail_18) (plus_4 x_42 (sum_4 tail_18))) 
      (case nil_4 z_4))))
(define-funs-rec
   ((sorted_4 ((l_24 list_4)) Bool))
   ((match l_24
      (case (cons_4 x_43 l2_5)
         (match l2_5
           (case (cons_4 y_24 l3_4)
              (and (leq_4 x_43 y_24) (sorted_4 (cons_4 y_24 l3_4)))) 
           (case nil_4 true))) 
      (case nil_4 true))))
(define-funs-rec
   ((map_4 ((f_6 (=> nat_4 nat_4)) (l_25 list_4)) list_4))
   ((match l_25
      (case (cons_4 x_44 tail_19) (cons_4 (f_6 x_44) (map_4 f_6 tail_19))) 
      (case nil_4 nil_4))))
(define-funs-rec ((num_1_2 () nat_4)) ((s_4 z_4)))
(define-funs-rec ((num_2_3 () nat_4)) ((s_4 num_1_2)))
(define-funs-rec ((num_3_3 () nat_4)) ((s_4 num_2_3)))
(define-funs-rec ((num_4_2 () nat_4)) ((s_4 num_3_3)))
(define-funs-rec ((num_5_2 () nat_4)) ((s_4 num_4_2)))
(define-funs-rec ((num_10_2 () nat_4)) ((mult_4 num_2_3 num_5_2)))
(assert-not
 (forall
    ((f_7 (=> nat_4 nat_4)))
    (not (and
          (=
           (map_4 f_7 
             (cons_4 num_1_2 (cons_4 num_2_3 (cons_4 num_3_3 nil_4))))
           (cons_4 num_3_3 (cons_4 num_4_2 (cons_4 num_5_2 nil_4)))) 
          (= (f_7 num_10_2) (plus_4 num_2_3 num_10_2))))))(check-sat)
