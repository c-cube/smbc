; expect: SAT

; goal is to find `f:(bool->bool)->bool->bool` such that `f not x=x`, `f id x=not x`

(declare-fun f ((=> Bool Bool) Bool) Bool)

(define-fun fid ((x Bool)) Bool x)
(define-fun fnot ((x Bool)) Bool (not x))

(assert (forall ((x Bool)) (= (f fnot x) x)))
(assert (forall ((x Bool)) (= (f fid x) (not x))))

(check-sat)
