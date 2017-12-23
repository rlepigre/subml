include "list.typ"
include "nat.typ"

type Rose(A) = μRose List(Rose)

val rec size : ∀A Rose(A) → Nat = fun l →
  case l of
  | []   → 0
  | x::l → S (add (size x) (size l))

val rec height : ∀A Rose(A) → Nat = fun l →
  case l of
  | []   → 0
  | x::l → let h1 = height x in
           let h2 = height l in
           S (max h1 h2)
