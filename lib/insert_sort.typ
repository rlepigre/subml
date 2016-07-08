type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]

type List(A) = μX F(A,X)

val rec insert0 : ∀o ∀A (A → A → Bool) →  A → List(A) →  List(A) =
  fun cmp a l →
    case l of
    | []   → a :: []
    | x::l → if cmp a x then a::l else x :: insert0 cmp a l

val rec insert : ∀o ∀A (A → A → Bool) → A → (μo X F(A,X)) → F(A, μo X F(A,X)) =
  fun cmp a l →
    case l of
    | []      → a :: []
    | x::l → if cmp a x then a::l else x :: insert cmp a l

val rec sort : ∀o ∀A  (A → A → Bool) → (μo X F(A,X)) → (μo X F(A,X)) =
  fun cmp l →
    case l of
    | []      → []
    | x::l → insert cmp x (sort cmp l)
