; generated by nunchaku
(declare-sort list 0)
(declare-sort term 0)
(declare-fun cons (term list) list)
(declare-fun b () term)
(declare-fun a () term)
(declare-fun nil () list)
(assert-not (= (cons a (cons b nil)) (cons b (cons a nil))))
(check-sat)

