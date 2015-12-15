(* Church numerals. *)
set verbose off

(* The type of natural numbers and the two basic constructors. *)
type Nat = ∀X ((X → X) → X → X)

val Z : Nat = fun s z ↦ z
val S : Nat → Nat = fun n f x ↦ f (n f x)

(* Names for the first 10 natural numbers. *)
val zero  : Nat = Z
val one   : Nat = S zero
val two   : Nat = S one
val three : Nat = S two
val four  : Nat = S three
val five  : Nat = S four
val six   : Nat = S five
val seven : Nat = S six
val eight : Nat = S seven
val nine  : Nat = S eight
val ten   : Nat = S nine

(* Addition and product. *)
val add : Nat → Nat → Nat = fun n m f x ↦ n f (m f x)
val mul : Nat → Nat → Nat = fun n m f ↦ n (m f)

(* Printing function. *)
val print_nat : Nat → {} = fun n ↦
  n (print("S"); (fun x -> x)) (print("Z\n"); {})

(* Predecessor. *)
val pred : Nat → Nat = fun n ↦
  n (fun p x y ↦ p (S x) x) (fun x y ↦ y) Z Z

(* Morley's inferior function. *)
include "lib/bool.typ"
type t = μX ((X → Bool) → Bool)
val leq : Nat → Nat → Bool = fun n m ↦
  (n : (t → t) → (t → t)) (fun f g ↦ g f) (fun i ↦ tru)
  ((m : (t → t) → (t → t)) (fun f g ↦ g f) (fun i ↦ fls))


include "lib/prod.typ"
val pred2 : Nat → Nat = fun n ↦ pi2 (n
        (fun p ↦  pair (S (pi1 p)) (pi1 p))
        (pair Z Z))

val pred3 : Nat → Nat = fun n ↦ n
        (fun p x y ↦ p (S x) x)
        (fun x y ↦ y) Z Z
