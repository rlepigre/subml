(* state monad, using Church encoding for pairs *)

include "lib/church/data.typ"

type State(V,X) = V → Pair(V,X)
type Unit = ∀X (X → X)

val unit : ∀X∀V(X → State(V,X)) = fun x v → pair v x
val bind : ∀X∀Y∀V (State(V,X) → (X → State(V,Y)) → State(V,Y)) =
  λn f v. n v (λv x. (f x v))
val read : ∀V∀X (State(V,X) → State(V,V)) =
  λn v.pair (pi1 (n v)) (pi1 (n v))
val write : ∀V (V → State(V,Unit)) =
  λx v. pair x (λx.x)
val run : ∀V∀X (State(V,X) → V  → X) = λn v. pi2 (n v)
