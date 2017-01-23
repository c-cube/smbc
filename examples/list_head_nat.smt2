
; expect: unsat
; variation on list_head, using natural numbers instead of uninterpreted type

(declare-datatypes () ((nat (Zero) (Succ (Pred nat)))))
(declare-datatypes
   ()
   ((list
       (Nil) 
       (Cons (select-Cons-0 nat) (select-Cons-1 list)))))
(define-fun-rec
   is_empty ((v_0 list)) Bool
     (match v_0 (case Nil true) 
                (case default false)))
(declare-const the_head nat) ; the "head" unknown
(define-fun-rec
   head ((list_0 list)) nat
     (match list_0
       (case (Cons nat_0 list_1) nat_0) 
       (case Nil the_head)))
(declare-fun l10 () list)
(declare-fun l21 () list)
(assert-not
 (or
  (not (is_empty l10)) 
  (not (is_empty l21)) 
  (= (head l10) (head l21))))
(check-sat)

