
; expect: SAT

; find a formula equivalent to f1 with 3 valuations

(include "logic.lisp")

; (not (a & (b | c))) | (not c & not d)
(define
  (f1 form
    (|
      (~(& (at a) (| (at b) (at c))))
      (& (~ (at c)) (~ (at d))))))

(define
  (v1
    (-> atom prop)
    (fun (x atom)
      (match x
        (a true)
        (b false)
        (c true)
        (d false)))))

(define
  (v2
    (-> atom prop)
    (fun (x atom)
      (match x
        (a false)
        (b false)
        (c false)
        (d true)))))

(define
  (v3
    (-> atom prop)
    (fun (x atom)
      (match x
        (a false)
        (b true)
        (c true)
        (d false)))))

(goal
  ((f2 form))
  (and
    (= (eval v1 f1) (eval v1 f2))
    (= (eval v2 f1) (eval v2 f2))
    (= (eval v3 f1) (eval v3 f2))))


