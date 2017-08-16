
; expect: SAT

; quantification that should evaluate to true
; forall x:nat. x=0 ∨ 0<x

(declare-datatypes () ((nat (s (select_s_0 nat))
                            (z))))

(define-funs-rec
  ((lt ((x nat)(y nat)) Bool))
  ((match x
    (case z (match y (case z false)(case (s y2) true)))
    (case (s x2) (match y (case z false)(case (s y2) (lt x2 y2)))))))

(assert-not
  (not (forall ((x nat)) (or (= x z) (lt z x)))))
