
; `l1 ++ l2 != l2 ++ l1`
; expect: SAT

(data (nat z (s nat)))

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

(goal ((l list)) (not (= l (rev l))))
