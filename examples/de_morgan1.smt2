
; expect: UNSAT

; try some formulas

(declare-datatypes ()
 ((atom (d) 
   (c) 
   (b) 
   (a))))
(declare-datatypes
   ()
   ((form
       (~ (select_~_0 form)) 
       (| (select_|_0 form) (select_|_1 form)) 
       (& (select_&_0 form) (select_&_1 form)) 
       (at (select_at_0 atom)))))
(define-funs-rec
   ((eval ((v (=> atom Bool)) (e form)) Bool))
   ((match e
      (case (~ a_1) (not (eval v a_1))) 
      (case (| a_2 b_1) (or (eval v a_2) (eval v b_1))) 
      (case (& a_3 b_2) (and (eval v a_3) (eval v b_2))) 
      (case (at a_4) (v a_4)))))
; (not (a & (b | c))) | (not c & not d)
(define-funs-rec
   ((f1 () form))
   ((| (~ (& (at a) (| (at b) (at c)))) (& (~ (at c)) (~ (at d))))))
; ((not a | not b) & (not a | not c)) | (not (c | d))
(define-funs-rec
   ((f2 () form))
   ((| (& (| (~ (at a)) (~ (at b))) (| (~ (at a)) (~ (at c)))) 
      (~ (| (at c) (at d))))))
; valuation
(define-funs-rec
   ((v1 ((x atom)) Bool))
   ((match x (case d false) 
             (case c true) 
             (case b false) 
             (case a true))))
(assert-not (= (eval v1 f1) (eval v1 f2)))
(check-sat)
