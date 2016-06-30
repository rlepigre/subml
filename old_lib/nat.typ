(* natural numbers using scott recursive encoding, typed *)
typed; inductive;
include "bool.typ";

type F_Nat(K) = ∀X ((K → X) → X → X);
type Nat = !K F_Nat(K);

let 0 = (fun f x ↦ x) : Nat;
let S n : Nat = (fun f x ↦ f n) : Nat;
let pred : Nat → Nat n = n (fun p ↦ p) 0;

type U(P) = ∀Y (Y → P);
type T(P) = ∀Y ((Y → U(P) → Y → P) → Y → P);
type Nat' = ∀P (T(P) → U(P) → T(P) → P);

fun x:Nat ↦ x:Nat';
let iter = ∀P fun a:P f: (P → P) n:Nat ↦
 n:Nat'
   (fun p r ↦ f (p r (fun r ↦ a):U(P) r)) : T(P)
   (fun r ↦ a):U(P)
   (fun p r ↦ f (p r (fun r ↦ a):U(P) r)) : T(P);

(*
type T(P) = ∀Y ((Y → P → P) → P);
let iter' = ∀P fun a:P f: (P → P) n:Nat ↦
 n:∀P (T(P) → P → P)
   ∀Y (fun p:(Y → P → P) ↦ f (p r a)) : T(P)
   a;
*)

type U(P) = ∀Y (Y → Nat → P);
type T(P) = ∀Y ((Y → U(P) → Y → Nat → P) → Y → Nat → P);
let recu = ∀P fun a:P f: (Nat → P → P) n:Nat ↦
 n:∀P (T(P) → U(P) → T(P) → Nat → P)
   (fun p r q ↦ f q (p r (fun r q ↦ a):U(P) r (pred q))) : T(P)
   (fun r q ↦ a):U(P)
   (fun p r q ↦ f q (p r (fun r q ↦ a):U(P) r (pred q))) : T(P)
   (pred n);

type U(P) = ∀Y (Y → Nat → P);
type T(P) = ∀Y ((Y → U(P) → Y → Nat → P) → Y → Nat → P);
let recu2 = ∀P fun a:P f: (Nat → P → P) n:Nat ↦
 n:∀P (T(P) → U(P) → T(P) → Nat → P)
   (fun p r q ↦ f (pred q) (p r (fun r q ↦ a):U(P) r q)) : T(P)
   (fun r q ↦ a):U(P)
   (fun p r q ↦ f (pred q) (p r (fun r q ↦ a):U(P) r q)) : T(P)
   n;

type G(P) = ∀K ((K → P) → (F_Nat(K) → P));
type U(P) = ∀K (K → P);
type T(P) = ∀K ((K → U(P) → K → P) → K → P);
let 0' = (fun f x ↦ x) : F_Nat(∀K K);
let S' = ∀K fun n:K ↦ (fun f x ↦ f n):F_Nat(K);
let Z : ∀P (G(P) -> U(P)) = fun f r ↦ f (fun x ↦ x) 0';
let Sc : /\P (/\K G(P) -> T(P)) =
  fun f p r ↦ f (fun s ↦ p r (Z f) r) (S' p);
let fix : /\P (/\K G(P) -> Nat -> P) = ∀P fun f:G(P) n:Nat ↦
 n:∀P (T(P) → U(P) → T(P) → P) (Sc f) (Z f) (Sc f);

(* fix f (S n) >
     (S n) (Sc f) (Z f) (Sc f) >
     (Sc f) n (Sc f) >
     f (n (Sc f) (Z f)) (S (Sc f)) >
     f (f ((P n) (Sc f) (Z f) *)
let 1 = S 0;
let 2 = S 1;
let 3 = S 2;
let 4 = S 3;
let 5 = S 4;
let 6 = S 5;
let 7 = S 6;
let 8 = S 7;
let 9 = S 8;
let 10 = S 9;


let add n m = iter n S m;
let mul n m = iter 0 (fun x ↦ add n x) m;
let 20 = add 10 10;
let 30 = add 20 10;
let 40 = add 30 10;
let 100 = mul 10 10;

recursive;

let rec eqN n:Nat m:Nat =
  n (λnp. m (λmp. eqN np mp) False) (m (λmp. False) True)
;
