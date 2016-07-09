type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]

type List(A) = μX F(A,X)

val rec insert : ∀α ∀A (A → A → Bool) → A → (μα X F(A,X)) → μα+1 X F(A,X) =
  fun cmp a l →
    case l of
    | []   → a :: []
    | x::l → if cmp a x then a::l else x :: insert cmp a l

val rec insert0 : ∀α ∀A (A → A → Bool) → A → List(A) →  List(A) =
  fun cmp a l →
    case l of
    | []   → a :: []
    | x::l → if cmp a x then a::l else x :: insert0 cmp a l

val insert1 : ∀α ∀A (A → A → Bool) →  A → List(A) →  List(A) = insert

val rec sort : ∀α ∀A  (A → A → Bool) → (μα X F(A,X)) → (μα X F(A,X)) =
  fun cmp l →
    case l of
    | []   → []
    | x::l → insert cmp x (sort cmp l)
