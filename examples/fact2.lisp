
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
       (let
         sub
         (fact n2)
         (mult n sub)))))))

(define
  (100 nat
   (let
     5
     (s (s (s (s (s z)))))
     (let 10 (mult (s (s z)) 5)
       (mult 10 10)))))

(goal
  ((n nat))
  (leq (mult 100 100) (fact n)))

