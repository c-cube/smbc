
; find `f` where: `map (f plus) [1,2,3] = [2,4,6], f 10=20`,

; expect: SAT
(declare-datatypes () ((nat_3 (s_3 (select_s_3_0 nat_3)) 
                              (z_3))))
(define-funs-rec
   ((plus_3 ((x_27 nat_3) (y_15 nat_3)) nat_3))
   ((match x_27 (case (s_3 x2_9) (s_3 (plus_3 x2_9 y_15))) 
                (case z_3 y_15))))
(define-funs-rec
   ((mult_3 ((x_28 nat_3) (y_16 nat_3)) nat_3))
   ((match x_28
      (case (s_3 x2_10) (plus_3 y_16 (mult_3 x2_10 y_16))) 
      (case z_3 z_3))))
(define-funs-rec
   ((leq_3 ((x_29 nat_3) (y_17 nat_3)) Bool))
   ((match x_29
      (case (s_3 x2_11)
         (match y_17 (case (s_3 y2_3) (leq_3 x2_11 y2_3)) 
                     (case z_3 false))) 
      (case z_3 true))))
(declare-datatypes
   ()
   ((list_3 (cons_3 (select_cons_3_0 nat_3) (select_cons_3_1 list_3)) 
            (nil_3))))
(define-funs-rec
   ((append_3 ((x_30 list_3) (y_18 list_3)) list_3))
   ((match x_30
      (case (cons_3 n_3 tail_12) (cons_3 n_3 (append_3 tail_12 y_18))) 
      (case nil_3 y_18))))
(define-funs-rec
   ((rev_3 ((l_16 list_3)) list_3))
   ((match l_16
      (case (cons_3 x_31 xs_3) (append_3 (rev_3 xs_3) (cons_3 x_31 nil_3))) 
      (case nil_3 nil_3))))
(define-funs-rec
   ((length_3 ((l_17 list_3)) nat_3))
   ((match l_17
      (case (cons_3 x_32 tail_13) (s_3 (length_3 tail_13))) 
      (case nil_3 z_3))))
(define-funs-rec
   ((sum_3 ((l_18 list_3)) nat_3))
   ((match l_18
      (case (cons_3 x_33 tail_14) (plus_3 x_33 (sum_3 tail_14))) 
      (case nil_3 z_3))))
(define-funs-rec
   ((sorted_3 ((l_19 list_3)) Bool))
   ((match l_19
      (case (cons_3 x_34 l2_4)
         (match l2_4
           (case (cons_3 y_19 l3_3)
              (and (leq_3 x_34 y_19) (sorted_3 (cons_3 y_19 l3_3)))) 
           (case nil_3 true))) 
      (case nil_3 true))))
(define-funs-rec
   ((map_3 ((f_4 (=> nat_3 nat_3)) (l_20 list_3)) list_3))
   ((match l_20
      (case (cons_3 x_35 tail_15) (cons_3 (f_4 x_35) (map_3 f_4 tail_15))) 
      (case nil_3 nil_3))))
(define-funs-rec ((num_1_1 () nat_3)) ((s_3 z_3)))
(define-funs-rec ((num_2_2 () nat_3)) ((s_3 num_1_1)))
(define-funs-rec ((num_3_2 () nat_3)) ((s_3 num_2_2)))
(define-funs-rec ((num_4_1 () nat_3)) ((s_3 num_3_2)))
(define-funs-rec ((num_5_1 () nat_3)) ((s_3 num_4_1)))
(define-funs-rec ((num_6_2 () nat_3)) ((s_3 num_5_1)))
(define-funs-rec ((num_10_1 () nat_3)) ((mult_3 num_2_2 num_5_1)))
(assert-not
 (forall
    ((f_5 (=> (=> nat_3 (=> nat_3 nat_3)) (=> nat_3 nat_3))))
    (not (and
          (=
           (map_3 (f_5 plus_3) 
             (cons_3 num_1_1 (cons_3 num_2_2 (cons_3 num_3_2 nil_3))))
           (cons_3 num_2_2 (cons_3 num_4_1 (cons_3 num_6_2 nil_3)))) 
          (= (f_5 plus_3 num_10_1) (mult_3 num_2_2 num_10_1))))))(check-sat)
