(* Church booleans. *)

(* The type of booleans and the two constants. *)
type CBool = ∀X (X → X → X)

val ctru : CBool = fun x y ↦ x
val cfls : CBool = fun x y ↦ y

(* Conditional. *)
val cond : ∀X (CBool → X → X → X) = fun c t e ↦ c t e

(* Basic operations. *)
val or  : CBool → CBool → CBool = fun a b ↦ a ctru b
val and : CBool → CBool → CBool = fun a b ↦ a b cfls
val xor : CBool → CBool → CBool = fun a b ↦ a (b cfls ctru) b

val not : CBool → CBool = fun a  ↦ a cfls ctru

(* Printing_function. *)
val print_bool : CBool → {} = fun b ↦
  b (print("ctru\n"); {}) (print("cfls\n"); {})
