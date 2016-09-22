
; uninterpreted functions
; expect: SAT

(decl-ty u)
(decl a u)
(decl b u)
(decl f (-> u prop))

(assert (not (= (f a) (f b))))

; u = {a,b}
(assert
  (forall (x u)
    (or (= x a) (= x b))))

(goal
  ((x u))
  (not (= (f x) (f b))))

