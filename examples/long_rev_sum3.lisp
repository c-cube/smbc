
; find a list `l` where: `length l = 10 & sum l = 20 & rev l = l`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(define (two nat (s (s z))))
(define (five nat (s (s (s (s (s z)))))))
(define (ten nat (mult two five)))
(define (twenty nat (mult two ten)))

(goal
  ((l list))
  (and
    (= (length l) ten)
    (= (sum l) twenty)
    (= (rev l) l)
  ))


