
; find a list `l` where: `length l = 6 & sum l = 10 & rev l = l`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(goal
  ((l list))
  (and
    (= (length l) (s (s (s (s (s (s z)))))))
    (= (sum l) (s (s (s (s (s (s (s (s (s (s z)))))))))))
    (= (rev l) l)
  ))

