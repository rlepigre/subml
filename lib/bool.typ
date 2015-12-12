(* Church booleans. *)
set verbose off

(* The type of booleans and the two constants. *)
type Bool = ∀X (X → X → X)

val tru : Bool = fun x y ↦ x
val fls : Bool = fun x y ↦ y

(* Conditional. *)
val if : ∀X (Bool → X → X → X) = fun c t e ↦ (c t e)

(* Basic operations. *)
val or  : Bool → Bool → Bool = fun a b ↦ (a tru b)
val and : Bool → Bool → Bool = fun a b ↦ (a b fls)
val xor : Bool → Bool → Bool = fun a b ↦ (a (b fls tru) a)

val not : Bool → Bool = fun a  ↦ (a fls tru)

(* Printing_function. *)
val print_bool : Bool → {} = fun b ↦
  b (print("tru\n"); {}) (print("fls\n"); {})
