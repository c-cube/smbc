
; find a list that is sorted, length=51, sum=11, rev l=l

; expect: UNSAT

(include "nat.lisp")
(include "list.lisp")

(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (plus 5 5)))
(define (50 nat (mult 5 10)))

(goal
  ((l list))
  (and
    (sorted l)
    (= l (rev l))
    (= (sum l) (s 10))
    (= (length l) (s 50))
  ))

