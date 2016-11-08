
; expect: UNSAT

; variant of long_rev_sum6 that triggers the same bug:
; ./smbc.native --check examples/bug3.lisp --dimacs /tmp/foo.cnf --depth-step 4

(include "nat.lisp")
(include "list.lisp")

(define (1 nat (s z)))
(define (2 nat (s (s z))))
(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (mult 2 5)))

(goal
  ((l list))
  (and
    (= (length l) 2)
    (= (sum l) (plus 10 5))
    (= (rev l) l)
  ))



