
; find a list `l` where: `length l = 1,000 & sum l = 1 & rev l = l`
; expect: UNSAT

(include "nat.lisp")
(include "list.lisp")

(define (1 nat (s z)))
(define (2 nat (s (s z))))
(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (mult 2 5)))
(define (100 nat (mult 10 10)))
(define (1000 nat (mult 10 100)))

(goal
  ((l list))
  (and
    (= (length l) 1000)
    (= (sum l) 1)
    (= (rev l) l)
  ))


