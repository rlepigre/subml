
type S(α,A) = να X.{} → A × X
type Stream(A) = S(∞,A)

val map : ∀A.∀B.(A → B) → ∀α.S(α,A) → S(α,B) =
  fun f →
    let rec aux = fun s _ →
      let (a,s') = s {} in
      (f a, aux s')
    in aux

val coiter : ∀X.∀A.X → (X → A) → (X → X) → Stream(A) =
  fun s0 f n →
    let rec aux = fun x _ → (f x, aux (n x)) in
    aux s0

val rec group : ∀A.Stream(A) → Stream(A×A) =
  fun s _ →
    let (a,s1) = s {} in
    let (b,s2) = s {} in
    ((a,b), group s2)

val map2 : ∀A.∀B.∀C.(A → B → C) → ∀α.S(α,A) → S(α,B) → S(α,C) =
  fun f →
    let rec aux = fun sa sb _ →
      let (a,sa') = sa {} in
      let (b,sb') = sb {} in
      (f a b, aux sa' sb')
    in aux

include "nat.typ"

val stream_add = map2 add

val stream_add0 : Stream(Nat) → Stream(Nat) → Stream(Nat) = stream_add

val rec stream_mul : ∀α.S(α,Nat) → S(α,Nat) → S(α,Nat) =
  fun sa sb _ →
    let (a,sa') = sa {} in
    let (b,sb') = sb {} in
    (mul a b, stream_add (stream_mul sa sb') (stream_mul sa' sb))

val stream_mul0 : Stream(Nat) → Stream(Nat) → Stream(Nat) = stream_mul

val rec forget : Nat → Stream(Nat) → Stream(Nat) = fun n s →
  case n of
  | Z → s
  | S p →
    let (a,s') = s {} in
    forget p s'

val tom : (Nat → Nat) → Stream(Nat) → Stream(Nat) = fun f s →
  let rec aux : Nat → Stream(Nat) → Stream(Nat) = fun n s _ →
    let (a,s') = s {} in
    (a, aux (S n) (forget (f n) s'))
  in
  aux Z s
