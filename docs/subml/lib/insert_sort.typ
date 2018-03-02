type F(A,X) = [Nil | Cons of { hd : A; tl : X }]

type SList(α,A) = μα X.F(A,X)
type List(A) = SList(∞,A)

val rec insert : ∀α.∀A.(A → A → Bool) → A → SList(α,A) → SList(α+1,A) =
  fun cmp a l →
    case l of
    | []   → a :: []
    | x::l' → if cmp a x then a::l else x :: insert cmp a l'

val rec insert0 : ∀α.∀A.(A → A → Bool) → A → List(A) →  List(A) =
  fun cmp a l →
    case l of
    | []   → a :: []
    | x::l' → if cmp a x then a::l else x :: insert0 cmp a l'

val insert1 : ∀A.(A → A → Bool) →  A → List(A) →  List(A) = insert

val rec sort : ∀α.∀A.(A → A → Bool) → SList(α,A) → SList(α,A) =
  fun cmp l →
    case l of
    | []   → []
    | x::l → insert cmp x (sort cmp l)

val sort1 : ∀A.(A → A → Bool) →  List(A) →  List(A) = sort

include "nat.typ"

eval sort ls (3::1::2::4::Nil)
