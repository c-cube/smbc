; expect: UNSAT

; a more difficult variant of sorted2

; find a sorted list of length 51, that is a palindrome, and has sum 11

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
(declare-datatypes
   ()
   ((list (cons (select_cons_0 nat) (select_cons_1 list)) 
          (nil))))
(define-funs-rec
   ((append ((x_3 list) (y_3 list)) list))
   ((match x_3 (case (cons n tail) (cons n (append tail y_3))) 
               (case nil y_3))))
(define-funs-rec
   ((rev ((l list)) list))
   ((match l
      (case (cons x_4 xs) (append (rev xs) (cons x_4 nil))) 
      (case nil nil))))
(define-funs-rec
   ((length ((l_1 list)) nat))
   ((match l_1 (case (cons x_5 tail_1) (s (length tail_1))) 
               (case nil z))))
(define-funs-rec
   ((sum ((l_2 list)) nat))
   ((match l_2 (case (cons x_6 tail_2) (plus x_6 (sum tail_2))) 
               (case nil z))))
(define-funs-rec
   ((sorted ((l_3 list)) Bool))
   ((match l_3
      (case (cons x_7 l2)
         (match l2
           (case (cons y_4 l3) (and (leq x_7 y_4) (sorted (cons y_4 l3)))) 
           (case nil true))) 
      (case nil true))))
(define-funs-rec ((num_5 () nat)) ((s (s (s (s (s z)))))))
(define-funs-rec ((num_10 () nat)) ((plus num_5 num_5)))
(define-funs-rec ((num_50 () nat)) ((mult num_5 num_10)))
(assert-not
 (forall
    ((l_5 list))
    (not (and
          (and (and (sorted l_5) (= l_5 (rev l_5))) (= (sum l_5) (s num_10))) 
          (= (length l_5) (s num_50))))))(check-sat)
