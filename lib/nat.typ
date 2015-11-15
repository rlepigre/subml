(* Church numerals. *)
set verbose off

(* The type of natural numbers and the two basic constructors. *)
type Nat = ∀X ((X → X) → X → X)

val Z = (fun s z ↦ z) : Nat
val S (n : Nat) = (fun f x ↦ f (n f x)) : Nat

(* Names for the first 10 natural numbers. *)
val zero  = Z
val one   = S zero
val two   = S one
val three = S two
val four  = S three
val five  = S four
val six   = S five
val seven = S six
val eight = S seven
val nine  = S eight
val ten   = S nine

(* Addition and product. *)
val add (n : Nat) (m : Nat) = (fun f x ↦ n f (m f x)) : Nat
val mul (n : Nat) (m : Nat) = (fun f ↦ n (m f)) : Nat

(* Printing function. *)
val print_nat (n : Nat) =
  (n (print("S"); fun x -> x) (print("Z\n"); {})) : {}

(* Predecessor. *)
val pred (n : Nat) =
  n (fun p x y ↦ p (S x) x) (fun x y ↦ y) Z Z

(* Morley's inferior function. *)
include "lib/bool.typ"
val leq (n : Nat) (m : Nat) =
  n (fun f g ↦ g f) (fun i ↦ tru) (m (fun f g ↦ g f) (fun i ↦ fls))

(*
include "prod.typ";
let pred = λn:Nat.pi2 (n
        (λp. pair (S (pi1 p)) (pi1 p))
        (pair 0 0));

let pred = λn:Nat.(n
        (λp.p (λx y p.p ((λn:Nat.(λf x.f (n f x))) x) x))
        (λp.p 0 0)):Prod(Nat,Nat) (λx y.y);
*)
