(* State monad, with an array (a list in fact) as state *)

include "list.typ"
include "nat.typ"

type State(T,X) = List(Nat × T) → List(Nat × T) × X

val unit : ∀X∀T X → State(T,X) = fun x l → (l, x)

val bind : ∀X∀Y∀T State(T,X) → (X → State(T,Y)) → State(T,Y) =
  fun t f l → let (l, x) = t l in f x l

val read : ∀X∀T Nat → (Option(T) → State(T,X)) → State(T,X) =
  λn f l. f (assoc (eq n) l) l

val write : ∀X∀T (Nat → T → State(T,{})) =
  λn x l. ((n,x)::l, {})

val run : ∀T∀X (State(T,X) → X) = λf. (f []).2
