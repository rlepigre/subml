type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]
type List(A) = μX F(A,X)

val rec append : ∀A (List(A) → List(A) → List(A)) =
  fun l1 l2 →
    case l1 of
    | []   → l2
    | x::l → x :: append l l2

val rec partition : ∀A ∀α (A → Bool) → (μα X F(A,X)) → (μα X F(A,X)) × (μα X F(A,X)) =
  fun test l →
    case l of
    | []   → ([], [])
    | x::l → let c = partition test l in
             if test x then ((x::c.1), c.2)
             else (c.2,(x::c.1))

val partition' : ∀A (A → Bool) → List(A) → List(A) × List(A) = partition

val rec sort : ∀A (A → A → Bool) → List(A) → List(A) =
  fun cmp l → case l of
  | []   → []
  | x::l → let test = cmp x in
           let c = partition test l in
           let below = sort cmp c.1 in
           let above = sort cmp c.2 in
           append below (x :: above)
