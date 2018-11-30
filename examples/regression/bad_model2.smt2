; expect: sat

(declare-datatypes () ((nat (zero) 
                          (Suc (select-Suc-0 nat)))))
(declare-datatypes () ((prod (Pair (select-Pair-0 nat) (select-Pair-1 nat)))))
(declare-sort int 0)
(declare-fun AbsInteg (prod) int)
(declare-fun RepInteg (int) prod)
(assert (forall ((a int)) (= a (AbsInteg (RepInteg a)))))
(define-fun-rec
   plus ((nat_0 nat) (nat_1 nat)) nat
     (match nat_0
       (case (Suc nat_0_0) (Suc (plus nat_0_0 nat_1))) 
       (case zero nat_1)))
(define-fun-rec
   intrel ((prod_0 prod) (prod_1 prod)) Bool
     (@
       (match prod_0
         (case (Pair x __0)
            (lambda  ((uu2 prod))
              (match uu2
                (case (Pair __1 __2) (= (plus __1 __2) (plus x __0)))))))
       prod_1))
(assert (forall ((a_0 int)) (intrel (RepInteg a_0) (RepInteg a_0))))
(define-fun-rec
   intrel_0 ((prod_0_0 prod) (prod_1_0 prod)) Bool
     (@
       (match prod_0_0
         (case (Pair __3 __4)
            (lambda  ((uu2_0 prod))
              (match uu2_0
                (case (Pair __5 __6) (= (plus __5 __6) (plus __3 __4)))))))
       prod_1_0))
(assert
 (forall
    ((a_1 int))
    (forall ((b int)) (=> (intrel_0 (RepInteg a_1) (RepInteg b)) (= a_1 b)))))
(declare-datatypes () ((unit (Unity))))
(declare-datatypes
   ()
   ((point2dext
       (point2dext1 (select-point2dext1-0 int) (select-point2dext1-1 int) 
         (select-point2dext1-2 unit)))))
(declare-fun x () int)
(declare-fun p () point2dext)
(declare-fun y () int)
(define-fun-rec
   xcupdate_spec_0 ((point2dext_1 point2dext)) point2dext
     (match point2dext_1
       (case (point2dext1 int_0 int_1 unit_2)
          (point2dext1 (@ (lambda  ((uu int)) x) int_0) int_1 unit_2))))
(assert-not (= (point2dext1 x y Unity) (xcupdate_spec_0 p)))
(check-sat)

