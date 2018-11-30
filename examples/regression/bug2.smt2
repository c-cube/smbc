
; expect: SAT

; model is not specified enough

(declare-datatypes () ((a (ZeroA) 
                             (SuccA (PredA a)))))
(declare-fun y () a)
(declare-fun x () a)
(assert (not (= x y)))
(declare-datatypes () ((list (Nil) 
                             (Cons (Cons_0 a) (Cons_1 list)))))
(declare-datatypes () ((prod (Pair (Pair_0 a) (Pair_1 a)))))
(declare-datatypes () ((plist (PNil) 
                              (PCons (PCons_0 prod) (PCons_1 plist)))))
(declare-fun xs () list)
(declare-fun ys () list)
(define-fun-rec
   zip ((xs_0 list) (ys_0 list)) plist
     (match xs_0
       (case (Cons x __1)
          (match ys_0
            (case (Cons __0 __2) (PCons (Pair x __0) (zip __1 __2))) 
            (case Nil PNil))) 
       (case Nil PNil)))
(define-fun-rec
   append ((xs_1 list) (ys_1 list)) list
     (match xs_1
       (case (Cons __3 __4) (Cons __3 (append __4 ys_1))) 
       (case Nil ys_1)))
(define-fun-rec
   rev ((xs_2 list)) list
     (match xs_2
       (case (Cons __6 __5) (append (rev __5) (Cons __6 Nil))) 
       (case Nil Nil)))
(assert-not (= (zip (Cons x xs) ys) (zip (rev (Cons x xs)) (rev ys))))

