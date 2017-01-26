
; find `f` where: `map f [1,2,3] = [2,4,6], f 10=20`
; expect: SAT
(declare-datatypes () ((nat_2 (s_2 (select_s_2_0 nat_2)) 
                              (z_2))))
(define-funs-rec
   ((plus_2 ((x_18 nat_2) (y_10 nat_2)) nat_2))
   ((match x_18 (case (s_2 x2_6) (s_2 (plus_2 x2_6 y_10))) 
                (case z_2 y_10))))
(define-funs-rec
   ((mult_2 ((x_19 nat_2) (y_11 nat_2)) nat_2))
   ((match x_19
      (case (s_2 x2_7) (plus_2 y_11 (mult_2 x2_7 y_11))) 
      (case z_2 z_2))))
(define-funs-rec
   ((leq_2 ((x_20 nat_2) (y_12 nat_2)) Bool))
   ((match x_20
      (case (s_2 x2_8)
         (match y_12 (case (s_2 y2_2) (leq_2 x2_8 y2_2)) 
                     (case z_2 false))) 
      (case z_2 true))))
(declare-datatypes
   ()
   ((list_2 (cons_2 (select_cons_2_0 nat_2) (select_cons_2_1 list_2)) 
            (nil_2))))
(define-funs-rec
   ((append_2 ((x_21 list_2) (y_13 list_2)) list_2))
   ((match x_21
      (case (cons_2 n_2 tail_8) (cons_2 n_2 (append_2 tail_8 y_13))) 
      (case nil_2 y_13))))
(define-funs-rec
   ((rev_2 ((l_11 list_2)) list_2))
   ((match l_11
      (case (cons_2 x_22 xs_2) (append_2 (rev_2 xs_2) (cons_2 x_22 nil_2))) 
      (case nil_2 nil_2))))
(define-funs-rec
   ((length_2 ((l_12 list_2)) nat_2))
   ((match l_12
      (case (cons_2 x_23 tail_9) (s_2 (length_2 tail_9))) 
      (case nil_2 z_2))))
(define-funs-rec
   ((sum_2 ((l_13 list_2)) nat_2))
   ((match l_13
      (case (cons_2 x_24 tail_10) (plus_2 x_24 (sum_2 tail_10))) 
      (case nil_2 z_2))))
(define-funs-rec
   ((sorted_2 ((l_14 list_2)) Bool))
   ((match l_14
      (case (cons_2 x_25 l2_3)
         (match l2_3
           (case (cons_2 y_14 l3_2)
              (and (leq_2 x_25 y_14) (sorted_2 (cons_2 y_14 l3_2)))) 
           (case nil_2 true))) 
      (case nil_2 true))))
(define-funs-rec
   ((map_2 ((f_2 (=> nat_2 nat_2)) (l_15 list_2)) list_2))
   ((match l_15
      (case (cons_2 x_26 tail_11) (cons_2 (f_2 x_26) (map_2 f_2 tail_11))) 
      (case nil_2 nil_2))))
(define-funs-rec ((num_1 () nat_2)) ((s_2 z_2)))
(define-funs-rec ((num_2_1 () nat_2)) ((s_2 num_1)))
(define-funs-rec ((num_3_1 () nat_2)) ((s_2 num_2_1)))
(define-funs-rec ((num_4 () nat_2)) ((s_2 num_3_1)))
(define-funs-rec ((num_5 () nat_2)) ((s_2 num_4)))
(define-funs-rec ((num_6_1 () nat_2)) ((s_2 num_5)))
(define-funs-rec ((num_10 () nat_2)) ((mult_2 num_2_1 num_5)))
(assert-not
 (forall
    ((f_3 (=> nat_2 nat_2)))
    (not (and
          (=
           (map_2 f_3 (cons_2 num_1 (cons_2 num_2_1 (cons_2 num_3_1 nil_2))))
           (cons_2 num_2_1 (cons_2 num_4 (cons_2 num_6_1 nil_2)))) 
          (= (f_3 num_10) (mult_2 num_2_1 num_10))))))(check-sat)
