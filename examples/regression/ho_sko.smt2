
(declare-datatypes () ((nat (Z) 
                            (S (s_0 nat)))))

(declare-fun f (nat) Bool)

(define-fun check () Bool
  (and (f Z) (not (f (S Z))) (f (S (S Z)))))
(define-fun the-goal () Bool check)
(assert (the-goal))
(check-sat)
