
; expect: sat

; find list with len=3, sum=5
; here we use quantifiers instead of meta variables

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
(declare-datatypes
   ()
   ((list (cons (select_cons_0 nat) (select_cons_1 list))
          (nil))))
(define-funs-rec
   ((length ((l_1 list)) nat))
   ((match l_1 (case (cons x_5 tail_1) (s (length tail_1)))
               (case nil z))))
(define-funs-rec
   ((sum ((l_2 list)) nat))
   ((match l_2 (case (cons x_6 tail_2) (plus x_6 (sum tail_2)))
               (case nil z))))
(define-funs-rec ((num_1 () nat)) ((s z)))
(define-funs-rec ((num_2 () nat)) ((s (s z))))
(define-funs-rec ((num_5 () nat)) ((s (s (s (s (s z)))))))
(define-funs-rec ((num_10 () nat)) ((mult num_2 num_5)))
(assert-not
 (not (exists
    ((l_5 list))
      (and
        (and (= (length l_5) (s num_2)) (= (sum l_5) num_5))))))
(check-sat)
