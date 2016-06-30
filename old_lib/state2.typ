typed;

#include "list.typ";
#include "nat.typ";
#include "prod.typ";

type V[W,T] = List[T];
type Var[W] = Nat;
type State[W,T,X] = Var[W] → V[W,T] → Prod3[Var[W],V[W,T],X];
type Unit = ∀X (X → X);

let unit : ∀X∀W∀T(X → State[W,T,X]) x = fun n v ↦ pair3 n v x;

let bind : ∀X∀Y∀W∀T (State[W,T,X] → (X → State[W,T,Y]) → State[W,T,Y]) =
  λt f n l. t n l (λn' l' x. f x n' l');

let read : ∀X∀W∀T
  (Var[W] → (T → State[W,T,X]) → State[W,T,X]) =
  λv f n l. pair3 n l (f (nth (sub n v) l) n l)
;

let write : ∀X∀W∀T
  (Var[W] → T → State[W,T,Unit]) =
  λv t n l. pair3 (S n) (cons t l) (f (nth (sub n v) l) n l)
;

let run : ∀V∀X (State[W,T,X] → V  → X) = λn v. pi2 (n v);
