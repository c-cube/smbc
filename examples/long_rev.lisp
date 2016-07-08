
; find a list of length 6, where `rev l = l`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(goal
  ((l list))
  (and
    (= (length l) (s (s (s (s (s (s z)))))))
    (= (rev l) l)))

