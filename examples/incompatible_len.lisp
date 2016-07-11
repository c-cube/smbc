
; len l1 = 3, len l2 = 2, len (rev (l1 ++ l2)) = 6
; expect: UNSAT

(include "list.lisp")
(include "nat.lisp")

(define (2 nat (s (s z))))
(define (3 nat (s (s (s z)))))
(define (6 nat (mult 2 3)))

(goal
  ((l1 list)
   (l2 list))
  (and
    (= (length l1) 3)
    (= (length l2) 2)
    (= (length (rev (append l1 l2))) 6)
  ))

