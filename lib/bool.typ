(* Church booleans. *)
set verbose off

(* The type of booleans and the two constants. *)
type Bool = ∀X (X → X → X)

val tru = (fun x y ↦ x) : Bool
val fls = (fun x y ↦ y) : Bool

(* Conditional. *)
val if (c : Bool) t e = c t e

(* Basic operations. *)
val or  (a : Bool) (b : Bool) = a tru b
val and (a : Bool) (b : Bool) = a b fls
val xor (a : Bool) (b : Bool) = a (b fls tru) a
val not (a : Bool) = a fls tru
