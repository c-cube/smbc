
(data (nat z (s nat)))

(data (list nil (cons nat list)))

(define (append (-> list list list))
  (fun (x list)
       (fun (y list)
        (match
          x
          (nil y)
          ((cons n tail) (cons n (append tail y)))))))

(goal ((l1 list) (l2 list)) (not (= (append l1 l2) (append l2 l1))))
