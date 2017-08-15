
; `l1 ++ l2 != l2 ++ l1`
; expect: SAT

(declare-datatypes () ((nat (s (select_s_0 nat)) 
                            (z))))
(declare-datatypes
   ()
   ((list (cons (select_cons_0 nat) (select_cons_1 list)) 
          (nil))))
(define-funs-rec
   ((append ((x list) (y list)) list))
   ((match x (case (cons n tail) (cons n (append tail y))) 
             (case nil y))))
(define-funs-rec
   ((rev ((l list)) list))
   ((match l
      (case (cons x_1 xs) (append (rev xs) (cons x_1 nil))) 
      (case nil nil))))
(assert-not (forall ((l_1 list)) (not (not (= l_1 (rev l_1))))))(check-sat)
