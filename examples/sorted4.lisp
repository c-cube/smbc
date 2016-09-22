
; find a list that is sorted, length=10, sum=20

; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (plus 5 5)))
(define (20 nat (plus 10 10)))

(goal
  ((l list))
  (and
    (sorted l)
    (= (sum l) 20)
    (= (length l) 10)
  ))

