
; find `n` where `n! >= 100 * 100`
; expect: SAT

(include "nat.lisp")

(define
  (fact
    (-> nat nat)
    (fun (n nat)
     (match n
      (z (s z))
      ((s n2)
         (mult n 
         (fact n2)))))))

(define (5 nat (s (s (s (s (s z)))))))
(define (10 nat (mult (s (s z)) 5)))
(define (100 nat (mult 10 10)))

(goal
  ((n nat))
  (leq (mult 100 100) (fact n)))

