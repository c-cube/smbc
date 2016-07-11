
; find a list `l` where: `length l = 2, rev l = l, sum l = 500`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(define (1 nat (s z)))
(define (2 nat (s (s z))))
(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (mult 2 5)))
(define (100 nat (mult 10 10)))
(define (500 nat (mult 5 100)))

(goal
  ((l list))
  (and
    (= (length l) 2)
    (= (sum l) 500)
    (= (rev l) l)
  ))



