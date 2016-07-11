
; theory of lists
; expect: SAT

(include "nat.lisp")

(data (list nil (cons nat list)))

(define
  (append
  (-> list list list)
  (fun (x list)
       (fun (y list)
        (match
          x
          (nil y)
          ((cons n tail) (cons n (append tail y))))))))

(define
  (rev
    (-> list list)
    (fun
      (l list)
      (match
        l
        (nil nil)
        ((cons x xs) (append (rev xs) (cons x nil)))))))

(define
  (length (-> list nat)
  (fun (l list)
    (match l
      (nil z)
      ((cons x tail) (s (length tail)))))))

(define
  (sum
    (-> list nat)
    (fun (l list)
      (match l
        (nil z)
        ((cons x tail) (plus x (sum tail)))))))

(define
  (sorted (-> list prop)
   (fun (l list)
     (match l
      (nil true)
      ((cons x l2)
        (match l2
          (nil true)
          ((cons y l3)
           (and (leq x y) (sorted (cons y l3))))))))))
