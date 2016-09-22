
; type checking of simply-typed λ calculus
; expect: SAT

(include "nat.lisp")

(data (ty (const nat) (arrow ty ty)))

(define (a ty (const z)))
(define (b ty (const (s z))))
(define (c ty (const (s (s z)))))

(data (ty_opt ty_none (ty_some ty)))

(data (env e_nil (e_cons ty env)))

; lambda-expressions (where `app` has the type argument explicit)
(data (expr (var nat) (lam expr) (app expr expr ty)))

; lookup in env
(define
  (at_index
   (-> nat env ty_opt)
   (fun (n nat)
    (fun (e env)
     (match n
      (z
        (match e
          (e_nil ty_none)
          ((e_cons ty e') (ty_some ty))))
      ((s n')
        (match e
          (e_nil ty_none)
          ((e_cons ty e') (at_index n' e')))))))))

; type-check
(define
  (ty_check
    (-> env expr ty prop)
    (fun (env env)
     (fun (e expr)
      (fun (ty ty)
       (match e
        ((app f arg ty_arg)
         (and
           (ty_check env f (arrow ty_arg ty))
           (ty_check env arg ty_arg)))
        ((lam e')
         (match ty
          ((arrow ty_arg ty_ret)
           (ty_check (e_cons ty_arg env) e' ty_ret))
          ((const x) false)))
        ((var n)
         (match (at_index n env)
          (ty_none false)
          ((ty_some ty_var) (= ty_var ty))))))))))

(goal
  ((e expr))
  (ty_check e_nil e
    (arrow (arrow b c) (arrow (arrow a b) (arrow a c)))))

