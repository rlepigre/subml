(* Church-encoded  error monad (option type). *)

type Err(A) = ∀X ((A → X) → X → X)

val error : ∀A Err(A) =
  fun _ err → err

(* Monadic operations. *)

val unit : ∀A A → Err(A) =
  fun n ok err → ok n

val bind : ∀A ∀B Err(A) → (A → Err(B)) → Err(B) =
  fun n f → n (fun x → f x) error

(* Default value in case of error. *)

val catch : ∀A ∀B Err(A) → (A → B) → B → B =
  fun e f d → e f d

(* Printing functions. *)

val printErr : ∀A (A → {}) → Err(A) → {} =
  fun pelt x → x (fun x _ → pelt x) (fun _ → print("Error")) {}

val printlnErr : ∀A (A → {}) → Err(A) → {} =
  fun pelt x → printErr pelt x; print("\n")
