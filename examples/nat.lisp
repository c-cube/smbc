
; theory of nat
; expect: SAT

(data (nat z (s nat)))

(define
  (plus
    (-> nat nat nat)
    (fun (x nat)
     (fun (y nat)
      (match x
        (z y)
        ((s x2) (s (plus x2 y))))))))

(define
  (mult
    (-> nat nat nat)
    (fun (x nat)
     (fun (y nat)
      (match x
        (z z)
        ((s x2) (plus y (mult x2 y))))))))

