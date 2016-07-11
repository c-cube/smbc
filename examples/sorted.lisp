
; find a list that is sorted, and where `sum l = 15,
; and where `6 >= len l >= 4`

; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(define (3 nat (s (s (s z)))))
(define (5 nat (s (s (s (s (s z)))))))

(goal
  ((l list))
  (and
    (sorted l)
    (= (sum l) (mult 3 5))
    (leq (s 3) (length l))
    (leq (length l) (s 5))
  ))

