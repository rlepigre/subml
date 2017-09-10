

(* not covariant, but accepted *)
type TS(α) = μα X [ App of X × X | Lam of X → X]
type T = TS(∞)

(* we can write some terms *)
val idt:T = Lam(fun x → x)
val delta:T = Lam(fun x → App(x,x))
val omega:T = App(delta,delta)
val deux:T = Lam(fun f → Lam(fun x → App(f,App(f,x))))

(* List library. *)
include "nat.typ"

(* Whnf is not typable ... *)
!val rec whnf:Nat→T→T = fun n t →
  case n of
  | Z → t
  | S n →
    (case t of
    | App(u,v) →
       let u = whnf n u in
       (case u of
       | Lam f -> whnf n (f v)
       | _ → App(u,v))
    | _ → t)
