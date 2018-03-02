(* State monad using Church-encoded pairs. *)

include "church/data.typ"

type State(S,A) = S → Pair(S,A)

(* Monadic operations. *)

val unit : ∀S ∀A A → State(S,A) =
  fun e s → pair s e

val bind : ∀S ∀A ∀B State(S,A) → (A → State(S,B)) → State(S,B) =
  fun a f s → a s (fun s e → f e s)

(* Unit type. *)

type U = ∀X (X → X)

val u : U = fun x → x

(* Read / write operations. *)

val read : ∀S ∀A State(S,A) → State(S,S) =
  fun a s → (fun v → pair v v) (pi1 (a s))

val write : ∀S S → State(S,U) =
  fun s _ → pair s u

(* Evaluation function. *)

val run : ∀S ∀A State(S,A) → S  → A =
  fun a s → pi2 (a s)
