
; find a list `l` where: `length l = 6 & sum l = 11 & rev l = l`
; unsat since the list must be symmetric, but 11 is odd

; expect: UNSAT

(include "nat.lisp")
(include "list.lisp")

(goal
  ((l list))
  (and
    (= (length l) (s (s (s (s (s (s z)))))))
    (= (sum l) (s (s (s (s (s (s (s (s (s (s (s z))))))))))))
    (= (rev l) l)
  ))

