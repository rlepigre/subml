(* List library. *)
include "lib/nat.typ"

type List(A) = μX [Nil of {} | Cons of {hd : A; tl : X}]

val cons : ∀A A → List(A) → List(A) = fun e l ↦ e::l

val nil : ∀A List(A) = Nil

val hd : ∀A List(A) → Option(A) = fun l ↦
  case l of
  | []   → None
  | x::l → Some x

val tl : ∀A (List(A) → Option(List(A))) = fun l ↦
  case l of
  | []   → None
  | x::l → Some l

val rec length : ∀A (List(A) → Nat) = fun l ↦
  case l of
  | []   → Z
  | x::l → S(length l)

val rec nth : ∀A (List(A) → Nat → Option(A)) = fun l n ↦
  case n of
  | Z   → hd l
  | S x → (case l of [] → None | a::l → nth l x)

val rec map : ∀A ∀B ((A → B) → List(A) → List(B)) = fun f l ↦
  case l of
  | []   → []
  | x::l → f x :: map f l

val rec append : ∀A (List(A) → List(A) → List(A)) = fun l1 l2 ↦
  case l1 of
  | []   → l2
  | x::l → x :: append l l2

val rec concat : ∀A (List(List(A)) → List(A)) = fun l ↦
  case l of
  | []      → []
  | x::l → append x (concat l)

val rec fold_left : ∀A ∀B ((B → A → B) → B → List(A) → B) = fun f e l ↦
  case l of
  | []      → e
  | x::l → fold_left f (f e x) l

val rec assoc : ∀A ∀B (A → Bool) → List(A × B) → Option(B) = fun f l ↦
  case l of
  | []      → None
  | x::l → if f x.1 then Some x.2 else (assoc f l)
