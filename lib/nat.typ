(* Church numerals. *)
set verbose off

(* The type of natural numbers and the two basic constructors. *)
type Nat = ∀X (X → X) → X → X

val z : Nat = fun s z ↦ z
val s : Nat → Nat = fun n f x ↦ f (n f x)

(* Names for the first 10 natural numbers. *)
val zero  : Nat = z
val one   : Nat = s zero
val two   : Nat = s one
val three : Nat = s two
val four  : Nat = s three
val five  : Nat = s four
val six   : Nat = s five
val seven : Nat = s six
val eight : Nat = s seven
val nine  : Nat = s eight
val ten   : Nat = s nine

(* Addition and product. *)
val add : Nat → Nat → Nat = fun n m f x ↦ n f (m f x)
val mul : Nat → Nat → Nat = fun n m f ↦ n (m f)

(* Printing function. *)
val print_nat : Nat → {} = fun n ↦
  n (print("S"); (fun x -> x)) (print("Z\n"); {})

(* Predecessor. *)
val pred : Nat → Nat = fun n ↦
  n (fun p x y ↦ p (s x) x) (fun x y ↦ y) z z

(* Maurey's inferior function. *)
include "lib/church_bool.typ"
val leq : Nat → Nat → Bool = fun n m ↦
  n (fun f g ↦ g f) (fun i ↦ tru)
  (m (fun f g ↦ g f) (fun i ↦ fls))


include "lib/prod.typ"
val pred2 : Nat → Nat = fun n ↦ pi2 (n
        (fun p ↦  pair (s (pi1 p)) (pi1 p))
        (pair z z))

val pred3 : Nat → Nat = fun n ↦ n
        (fun p x y ↦ p (s x) x)
        (fun x y ↦ y) z z
