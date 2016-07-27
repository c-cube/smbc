
; `n = n+2`
; expect: UNSAT

(include "nat.lisp")

(goal
  ((n nat))
  (= n (s (s n))))
