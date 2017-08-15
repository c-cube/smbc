
; mini-sat solver
; expect: unsat

(declare-datatypes () ((atom (True) (False))))

(declare-datatypes ()
  ((form (A (bvar atom)) (And (and1 form) (and2 form)) (Not (not1 form)))))

(define-fun bimply ((f1 form) (f2 form)) form
  (Not (And f1 (Not f2))))

(define-fun-rec eval ((f form)) Bool
  (match f
    (case (A atom)
      (match atom (case True true) (case False false)))
    (case False false)
    (case (Not f) (not (eval f)))
    (case (And f1 f2) (and (eval f1) (eval f2)))))

(assert-not
  (forall ((a atom) (b atom))
    (eval (bimply (bimply (A a) (A b)) (bimply (Not (A b)) (Not (A a)))))))


