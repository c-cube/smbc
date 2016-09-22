
; expect: UNSAT

; try some formulas

(include "logic.lisp")

; (not (a & (b | c))) | (not c & not d)
(define
  (f1 form
    (|
      (~(& (at a) (| (at b) (at c))))
      (& (~ (at c)) (~ (at d))))))

; ((not a | not b) & (not a | not c)) | (not (c | d))
(define
  (f2 form
    (|
      (&
        (| (~ (at a)) (~ (at b)))
        (| (~ (at a)) (~ (at c))))
      (~ (| (at c) (at d))))))

(define
  (v1
    (-> atom prop)
    (fun (x atom)
      (match x
        (a true)
        (b false)
        (c true)
        (d false)))))

(goal ()
  (not
    (= (eval v1 f1) (eval v1 f2))))

