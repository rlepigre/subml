(* Examples that must obviously fail. *)

val delta : ∀X (∀X X) → X = fun x → x x

!val omega = delta delta
!val omega = (fun x -> x x) (fun x -> x x)

(* NOTE: delta is typable, but cannot be applied. *)

(* Inductive type not satisfying the usual positivity cryterion. *)

type A = μX [C of X → X]

!val delta : A → A = fun x → case x of C (f : A → A) → f x

(* Coinductive type not satisfying the usual positivity cryterion. *)

type B = νX [C of X → X]

val delta : B → B = fun x → case x of C (f : B → B) → f x

!val omega : {} → A = fun _ → delta (C delta)

(* NOTE: delta is typable. *)
