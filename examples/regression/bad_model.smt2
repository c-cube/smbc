; expect: sat

(declare-sort a_ 0)
(declare-datatypes
   ()
   ((list_ (Nil_) 
           (Cons_ (select-Cons_-0 a_) (select-Cons_-1 list_)))))
(declare-fun xs_ () list_)
(define-fun-rec
   append_ ((list__0 list_) (list__1_0 list_)) list_
     (match list__0
       (case (Cons_ a__0 list__1) (Cons_ a__0 (append_ list__1 list__1_0))) 
       (case Nil_ list__1_0)))
(define-fun-rec
   rev_ ((list__0_0 list_)) list_
     (match list__0_0
       (case (Cons_ a__0_0 list__1_1)
          (append_ (rev_ list__1_1) (Cons_ a__0_0 Nil_))) 
       (case Nil_ Nil_)))
(assert-not (or (not (= (rev_ (rev_ xs_)) xs_)) (= xs_ Nil_)))
(check-sat)

