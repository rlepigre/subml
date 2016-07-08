(* Append list library. *)
type AList(A) = μX
  [Nil | Cons of {hd : A ; tl : X} | App of {left : X ; right : X}]

val emptyAList : ∀X AList(X) = Nil

val consAList : ∀X X → AList(X) → AList(X) =
  fun e l ↦ e::l

val appendAList : ∀X AList(X) → AList(X) → AList(X) =
  fun l1 l2 ↦ App{left = l1; right = l2}
(*
val rec hdAList : ∀X AList(X) → Option(X) = fun l ↦
  case l of
  | Nil     → None
  | Cons[c] → Some[c.hd]
  | App[c]  →
    (case hdAList c.left of
     | None    → hdAList c.right
     | Some[e] → Some[e])

val rec tlAList : ∀X AList(X) → Option(AList(X)) = fun l ↦
  case l of
  | Nil     → None
  | Cons[c] → Some[c.tl]
  | App[c]  →
    (case tlAList c.left of
     | None    → tlAList c.right
     | Some[e] → Some[appendAList e c.right])

val rec mapAList : ∀X ∀Y (X → Y) → AList(X) → AList(Y) = fun f l ↦
  case l of
  | Nil     → Nil
  | Cons[c] → Cons[{hd = f c.hd; tl = mapAList f c.tl}]
  | App[c]  → App[{left = mapAList f c.left; right = mapAList f c.right}]

include "lib/list.typ"

(* A term in the type List(A) can be used as a term type AList(A). *)
val fromList : ∀X List(X) → AList(X) = fun l ↦ l

(* It is obviously not true in the other way... *)
val rec toList : ∀X AList(X) → List(X) = fun l ↦
  case l of
  | Nil     → Nil
  | Cons[c] → Cons[{hd = c.hd; tl = toList c.tl}]
  | App[c]  → append (toList c.left) (toList c.right)
*)