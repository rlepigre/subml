(* Append list library. *)
type AList(A) =
  μX.[Nil | Cons of {hd : A ; tl : X} | App of {left : X ; right : X}]

val emptyAList : ∀X.AList(X) = []

val consAList : ∀X.X → AList(X) → AList(X) =
  fun e l → e::l

val appendAList : ∀X.AList(X) → AList(X) → AList(X) =
  fun l1 l2 → App{left = l1; right = l2}

val rec hdAList : ∀X.AList(X) → Option(X) = fun l →
  case l of
  | []                  → None
  | e::l                → Some e
  | App{left=l;right=r} →
    (case hdAList l of
     | None   → hdAList r
     | Some e → Some e)

val rec tlAList : ∀X.AList(X) → Option(AList(X)) = fun l →
  case l of
  | []                   → None
  | e::l                 → Some l
  | App{left=l;right=r}  →
    (case tlAList l of
     | None   → tlAList r
     | Some e → Some(appendAList e r))

val rec mapAList : ∀X.∀Y.(X → Y) → AList(X) → AList(Y) = fun f l →
  case l of
  | []                  → []
  | e::l                → f e :: mapAList f l
  | App{left=l;right=r} → App{left = mapAList f l; right = mapAList f r}

include "list.typ"

(* A term in the type List(A) can be used as a term type AList(A). *)
val fromList : ∀X.List(X) → AList(X) = fun l → l

(* It is obviously not true in the other way... *)
val rec toList : ∀X.AList(X) → List(X) = fun l →
  case l of
  | []                  → []
  | e::l                → e::toList l
  | App{left=l;right=r} → append (toList l) (toList r)
