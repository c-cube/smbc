
; basic propositional formulas
; expect: sat

(data (atom a b c d))

(data (form (at atom) (& form form) (| form form) (~ form)))

; evaluate a formula (v: valuation)
(define
  (eval
    (-> (-> atom prop) form prop)
    (fun (v (-> atom prop))
      (fun (e form)
        (match e
          ((at a) (v a))
          ((& a b) (and (eval v a) (eval v b)))
          ((| a b) (or (eval v a) (eval v b)))
          ((~ a) (not (eval v a))))))))

