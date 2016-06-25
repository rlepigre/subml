type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]

type List(A) = μX F(A,X)

val rec insert0 : ∀o ∀A (A → A → Bool) →  A → List(A) →  List(A) =
  fun cmp a l →
    case l of
    | []      → a :: []
    | Cons[c] → if cmp a c.hd then a::l else c.hd :: insert0 cmp a c.tl

val rec insert : ∀o ∀A (A → A → Bool) → A → (μo X F(A,X)) → F(A, μo X F(A,X)) =
  fun cmp a l →
    case l of
    | []      → a :: []
    | Cons[c] → if cmp a c.hd then a::l else c.hd :: insert cmp a c.tl

val rec sort : ∀o ∀A  (A → A → Bool) → (μo X F(A,X)) → (μo X F(A,X)) =
  fun cmp l →
    case l of
    | Cons[c] → insert cmp c.hd (sort cmp c.tl)
    | []      → []
