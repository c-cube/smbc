
; type checking of simply-typed λ calculus
; expect: SAT
(declare-datatypes () ((nat (s (select_s_0 nat)) 
                            (z))))
(define-funs-rec
   ((plus ((x nat) (y nat)) nat))
   ((match x (case (s x2) (s (plus x2 y))) 
             (case z y))))
(define-funs-rec
   ((mult ((x_1 nat) (y_1 nat)) nat))
   ((match x_1 (case (s x2_1) (plus y_1 (mult x2_1 y_1))) 
               (case z z))))
(define-funs-rec
   ((leq ((x_2 nat) (y_2 nat)) Bool))
   ((match x_2
      (case (s x2_2) (match y_2 (case (s y2) (leq x2_2 y2)) 
                                (case z false))) 
      (case z true))))
(declare-sort ty-const 0)
(declare-fun k_a () ty-const)
(declare-fun k_b () ty-const)
(declare-fun k_c () ty-const)
(assert (not (= k_a k_b)))
(assert (not (= k_a k_c)))
(assert (not (= k_b k_c)))
(declare-datatypes
   ()
   ((ty
       (arrow (select_arrow_0 ty) (select_arrow_1 ty)) 
       (const (select_const_0 ty-const)))))
(define-funs-rec ((a () ty)) ((const k_a)))
(define-funs-rec ((b () ty)) ((const k_b)))
(define-funs-rec ((c () ty)) ((const k_c)))
(declare-datatypes () ((ty_opt (ty_some (select_ty_some_0 ty)) 
                               (ty_none))))
(declare-datatypes
   ()
   ((env (e_cons (select_e_cons_0 ty) (select_e_cons_1 env)) 
         (e_nil))))
(declare-datatypes
   ()
   ((expr
       (app (select_app_0 expr) (select_app_1 expr) (select_app_2 ty)) 
       (lam (select_lam_0 expr)) 
       (var (select_var_0 nat)))))
(define-funs-rec
   ((at_index ((n nat) (e env)) ty_opt))
   ((match n
      (case (s n_)
         (match e
           (case (e_cons ty_1 e_) (at_index n_ e_)) 
           (case e_nil ty_none))) 
      (case z
         (match e
           (case (e_cons ty_2 e__1) (ty_some ty_2)) 
           (case e_nil ty_none))))))
(define-funs-rec
   ((ty_check ((env_1 env) (e_1 expr) (ty_3 ty)) Bool))
   ((match e_1
      (case (app f arg ty_arg)
         (and
          (ty_check env_1 f (arrow ty_arg ty_3)) 
          (ty_check env_1 arg ty_arg))) 
      (case (lam e__2)
         (match ty_3
           (case (arrow ty_arg_1 ty_ret)
              (ty_check (e_cons ty_arg_1 env_1) e__2 ty_ret)) 
           (case (const x_3) false))) 
      (case (var n_1)
         (match (at_index n_1 env_1)
           (case (ty_some ty_var) (= ty_var ty_3)) 
           (case ty_none false))))))
(assert-not
 (forall
    ((e_2 expr))
    (not (ty_check e_nil e_2 
           (arrow (arrow b c) (arrow (arrow a b) (arrow a c)))))))(check-sat)
