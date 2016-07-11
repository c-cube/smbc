
; find a list that is sorted, length=3, sum=1, rev l=l

; expect: UNSAT

(include "nat.lisp")
(include "list.lisp")

(define (3 nat (s (s (s z)))))

(goal
  ((l list))
  (and
    (sorted l)
    (= l (rev l))
    (= (sum l) (s z))
    (= (length l) 3)
  ))

