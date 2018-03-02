(* This example requires a “max” operator on ordinals, which was included at
   some point. It will probably be added again in a future version. *)

include "prelude.typ"

type SNat(α) = μα N [ Z | S of N ]

(*
val if_max : ∀α ∀β Bool → SNat(α) → SNat(β) → SNat(max(α,β)) =
  fun b n m → if b then n else m

val fst : ∀α ∀β SNat(α) → SNat(β) → SNat(max(α,β)) =
  fun x y → x

val snd : ∀α ∀β SNat(α) → SNat(β) → SNat(max(α,β)) =
  fun x y → y

val rec max : ∀α ∀β SNat(α) → SNat(β) → SNat(max(α,β)) =
  fun n m →
    case n of
    | Z    → m
    | S n' → (case m of Z → n | S m' → S (max n' m'))
*)
