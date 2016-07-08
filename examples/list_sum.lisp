
; find a list whose sum = 4, where `rev l = l`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(goal
  ((l list))
  (and
    (= (sum l) (s (s (s (s z)))))
    (= (rev l) l)
  ))

