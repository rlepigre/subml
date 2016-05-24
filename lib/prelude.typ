(****************************************************************************)
(*                               Booleans.                                  *)
(****************************************************************************)
type Bool = [Tru | Fls]

val tru : Bool = Tru
val fls : Bool = Fls

(* Condition function. Prefer the use of syntax "if ... then ... else ...". *)
val cond : ∀X Bool → X → X → X = fun c t e ↦
  case c of Tru → t | Fls → e

val or : Bool → Bool → Bool = fun a b ↦
  if a then tru else b

val and : Bool → Bool → Bool = fun a b ↦
  if a then b else fls

val neg : Bool → Bool = fun a ↦
  if a then fls else tru

(****************************************************************************)
(*                               Option type.                               *)
(****************************************************************************)
type Option(A) = [None | Some of A]

val map_option : ∀X ∀Y (X → Y) → Option(X) → Option(Y) = fun f o ↦
  case o of
  | None    → None
  | Some[x] → Some[f x]

val from_option : ∀X Option(X) → X → X = fun o d ↦
  case o of
  | None    → d
  | Some[x] → x

(****************************************************************************)
(*             A standard return type for comparing functions.              *)
(****************************************************************************)
type Cmp = [Ls | Eq | Gt]

(****************************************************************************)
(*                             Common functions.                            *)
(****************************************************************************)
val id  : ∀X X → X        = fun x ↦ x
val fst : ∀X ∀Y X → Y → X = fun x y ↦ x
val snd : ∀X ∀Y X → Y → Y = fun x y ↦ y

val compose : ∀X ∀Y ∀Z (Y → Z) → (X → Y) → X → Z = fun f g x ↦ f (g x)
