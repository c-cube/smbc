
; len l1 = 5 & len l2 = 5 & sum (l1 ++ l2) = 16 & rev (l1 ++ l2) = l1 ++ l2
; expect: SAT

(include "list.lisp")
(include "nat.lisp")

(define (5 nat (s (s (s (s (s z)))))))
(define (3 nat (s (s (s z)))))
(define (15 nat (mult 3 5)))

(goal
  ((l1 list)
   (l2 list))
  (and
    (= (length l1) 5)
    (= (length l2) 5)
    (= (sum (append l1 l2)) (s 15))
    (= (rev (append l1 l2)) (append l1 l2))
  ))

