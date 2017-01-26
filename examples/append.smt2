
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
(assert-not
 (forall ((l1 list) (l2 list)) (= (append l1 l2) (append l2 l1))))
 (check-sat)
