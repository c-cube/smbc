; expect SAT

(declare-sort iota 0)
(declare-datatypes
   ()
   ((list_iota
       (cons_iota (cons_iota_0 iota) (cons_iota_1 list_iota)) 
       (nil_iota))))
(declare-datatypes () ((nat (z) 
                            (s (s_0 nat)))))
(define-fun-rec
   take_iota ((v_0 nat) (l list_iota)) list_iota
     (match v_0
       (case (s n)
          (match l
            (case nil_iota nil_iota) 
            (case (cons_iota x l_0) (cons_iota x (take_iota n l_0))))) 
       (case z nil_iota)))
(declare-fun nun_sk_0 () list_iota)
(declare-fun nun_sk_1 () iota)
(declare-fun nun_sk_2 () iota)
(declare-fun nun_sk_3 () iota)
(declare-fun nun_sk_4 () list_iota)
(assert-not
 (not (= (take_iota (s (s (s z))) nun_sk_0)
       (cons_iota nun_sk_1 (cons_iota nun_sk_2 (cons_iota nun_sk_3 nun_sk_4))))))

