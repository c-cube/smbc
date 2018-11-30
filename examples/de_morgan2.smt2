
; expect: SAT

; find a formula equivalent to f1 with 3 valuations
(declare-datatypes () ((atom_1 (d_1) 
                               (c_1) 
                               (b_3) 
                               (a_5))))
(declare-datatypes
   ()
   ((form_1
       (~_1 (select_~_1_0 form_1)) 
       (or__1 (select_or_1_0 form_1) (select_or_1_1 form_1)) 
       (&_1 (select_&_1_0 form_1) (select_&_1_1 form_1)) 
       (at_1 (select_at_1_0 atom_1)))))
(define-funs-rec
   ((eval_1 ((v_1 (=> atom_1 Bool)) (e_1 form_1)) Bool))
   ((match e_1
      (case (~_1 a_6) (not (eval_1 v_1 a_6))) 
      (case (or__1 a_7 b_4) (or (eval_1 v_1 a_7) (eval_1 v_1 b_4))) 
      (case (&_1 a_8 b_5) (and (eval_1 v_1 a_8) (eval_1 v_1 b_5))) 
      (case (at_1 a_9) (v_1 a_9)))))
; (not (a & (b | c))) | (not c & not d)
(define-funs-rec
   ((f1_1 () form_1))
   ((or__1 (~_1 (&_1 (at_1 a_5) (or__1 (at_1 b_3) (at_1 c_1)))) 
      (&_1 (~_1 (at_1 c_1)) (~_1 (at_1 d_1))))))
(define-funs-rec
   ((v1_1 ((x_1 atom_1)) Bool))
   ((match x_1
      (case d_1 false) 
      (case c_1 true) 
      (case b_3 false) 
      (case a_5 true))))
(define-funs-rec
   ((v2 ((x_2 atom_1)) Bool))
   ((match x_2
      (case d_1 true) 
      (case c_1 false) 
      (case b_3 false) 
      (case a_5 false))))
(define-funs-rec
   ((v3 ((x_3 atom_1)) Bool))
   ((match x_3
      (case d_1 false) 
      (case c_1 true) 
      (case b_3 true) 
      (case a_5 false))))
(assert-not
 (forall
    ((f2_1 form_1))
    (not (and
          (and
           (= (eval_1 v1_1 f1_1) (eval_1 v1_1 f2_1)) 
           (= (eval_1 v2 f1_1) (eval_1 v2 f2_1))) 
          (= (eval_1 v3 f1_1) (eval_1 v3 f2_1))))))
(check-sat)
