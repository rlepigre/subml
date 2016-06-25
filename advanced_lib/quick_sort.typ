type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]
type List(A) = μX F(A,X)

val rec partition : ∀A∀o (A → Bool) → (μo X F(A,X)) → (μo X F(A,X)) × (μo X F(A,X)) =
  fun test l →
    case l of
    | []      → ([], [])
    | Cons[l] → let c = partition test l.tl in
                if test l.hd then ((l.hd::c.1), c.2)
                else (c.2,(l.hd::c.1))

val partition' : ∀A (A → Bool) → List(A) → List(A) × List(A) = partition

val rec append : ∀A List(A) → List(A) → List(A) =
  fun l1 l2 →
    case l1 of
    | []      → l2
    | Cons[l] → l.hd :: append l.tl l2

val rec sort : ∀A (A → A → Bool) → List(A) → List(A) =
  fun cmp l → case l of
  | []      → []
  | Cons[l] → let test = cmp l.hd in
              let c = partition test l.tl in
              let above = sort cmp c.2 in
              let below = sort cmp c.1 in
              append below (l.hd :: above)
