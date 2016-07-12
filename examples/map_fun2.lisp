
; find `f` where: `map f [1,2,3] = [2,4,6], f 10=20`
; expect: SAT

(include "nat.lisp")
(include "list.lisp")

(define (1 nat (s z)))
(define (2 nat (s 1)))
(define (3 nat (s 2)))
(define (4 nat (s 3)))
(define (5 nat (s 4)))
(define (6 nat (s 5)))
(define (10 nat (mult 2 5)))

(goal
  ((f (-> nat nat)))
  (and
    (=
      (map f (cons 1 (cons 2 (cons 3 nil))))
      (cons 2 (cons 4 (cons 6 nil))))
    (= (f 10) (mult 2 10))
  ))


