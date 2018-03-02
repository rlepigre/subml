type TS(α,V) = μα T.[App of T * T | Lam of V → T | Var of V]
type T(V) = TS(∞,V)
type Term = ∀V.T(V) (* closed term *)

val idt : Term = Lam(fun x → Var x)
val delta : Term = Lam(fun x → App (Var x, Var x))
val zero : Term = Lam(fun f → Lam(fun x → Var x))
val succ : Term = Lam(fun n → Lam(fun f → Lam(fun x → App(Var f, App(App(Var n,Var f),Var x)))))
val one : Term = App(succ,zero)
val two : Term = App(succ,one)

val rec subst : ∀V.T(Option(V)) → Term → T(V) = fun f x →
  case f of
  | Var v → (case v of None → x | Some v → Var v)
  | App(t1,t2) → App(subst t1 x, subst t2 x)
  | Lam(f) → Lam(fun y → subst (f (Some y)) x)

type S(A,V) = [Subst of A | Keep of V]

val rec subst2 : ∀V.T(S(Term,V)) → T(V) = fun f →
  case f of
  | Var v → (case v of Keep v → Var v | Subst t → t)
  | App(t1,t2) → App(subst2 t1, subst2 t2)
  | Lam(f) → Lam(fun y → subst2 (f (Keep y)))

val rec squish : ∀γ.∀V.(TS(γ,T(V)) → T(V)) = fun f →
  case f of
  | Var v → v
  | App(t1,t2) → App(squish t1, squish t2)
  | Lam(f) → Lam(fun y → squish (f (Var y)))

val subst3 : ∀V.(T(V) → T(T(V))) → T(V) → T(V) =
  fun f → fun t → squish (f t)

check ∀V.(T(V) → T(V)) ⊂ Term → Term

val argu : Term → Term = (fun t →
  case t of App(_,t) → t | t → t) : ∀V.(T(V) → T(V))

val func : Term → Term = (fun t →
  case t of App(t,_) → t | t → t) : ∀V.(T(V) → T(V))

val rec whnf_step : ∀α.∀V.TS(α,T(V)) → T(V) = fun t →
  case t of
  | App(t1,t2) →
    (case t1 of
     | Lam(f) → subst3 f (squish t2)
     | _      → App(whnf_step t1, squish t2))
  | Lam f → Lam (fun v → whnf_step (f (Var v)))
  | Var v → v

val whnf_step : Term → Term = whnf_step

include "nat.typ"

val rec whnf_steps : Nat → Term → Term = fun n t →
  case n of Z → t | S p → whnf_steps p (whnf_step t)

eval (whnf_steps 3 (App(delta,idt)))

eval (whnf_steps 10 (App(two,two)))

(*
Lam λv.squish ((λv.squish ((λv.squish ((λv.squish ((λv.squish ((λv.squish ((λv.squish ((λv.squish ((λy.squish ((λy.squish ((λx.App (Var Var App (Lam λy.squish ((λy.squish ((λn.Lam λf.Lam λx.App (Var f, App (App (Var n, Var f), Var x))) Var y)) Var y), App (Lam λy.squish ((λy.squish ((λn.Lam λf.Lam λx.App (Var f, App (App (Var n, Var f), Var x))) Var y)) Var y), Lam λy.squish ((λy.squish ((λf.Lam λx.Var x) Var y)) Var y))), App (App (Var App (Lam λy.squish ((λn.Lam λf.Lam λx.App (Var f, App (App (Var n, Var f), Var x))) Var y), Lam λy.squish ((λf.Lam λx.Var x) Var y)), Var Var App (Lam λy.squish ((λy.squish ((λn.Lam λf.Lam λx.App (Var f, App (App (Var n, Var f), Var x))) Var y)) Var y), App (Lam λy.squish ((λy.squish ((λn.Lam λf.Lam λx.App (Var f, App (App (Var n, Var f), Var x))) Var y)) Var y), Lam λy.squish ((λy.squish ((λf.Lam λx.Var x) Var y)) Var y)))), Var x))) Var y)) Var y)) Var v)) Var v)) Var v)) Var v)) Var v)) Var v)) Var v)) Var v) : Term
*)
