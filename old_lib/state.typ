(* state monad, using Church encoding for pairs *)
typed;

type State(V,X) = V → Prod(V,X);
type Unit = ∀X (X → X);

let unit : ∀X∀V(X → State(V,X)) x = fun v => pair v x;
let bind : ∀X∀Y∀V (State(V,X) → (X → State(V,Y)) → State(V,Y)) =
  λn f v. n v (λv x. (f x v));
let read : ∀V∀X (State(V,X) → State(V,V)) =
  λn v.pair (pi1 (n v)) (pi1 (n v));
let write : ∀V (V → State(V,Unit)) =
  λx v. pair x (λx.x);
let run : ∀V∀X (State(V,X) → V  → X) = λn v. pi2 (n v);
