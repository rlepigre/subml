(* unary natural with sums encoded using records *)
typed; inductive;

type Nat = μK ∀X ({ Z : X ; S : K -> X} -> X) ;

let 0 : Nat = fun r ↦ r.Z ;
let succ : Nat → Nat = fun n r ↦ r.S n ;

# test du sous-typage
type Rel = μK ∀X ({ Z : X ; S : K -> X ; P : K -> X } -> X) ;
let natrel : Nat → Rel = fun n ↦ n ;

#iterateur sans point fixe
type T(P) = ∀Y (( { Z : Y → P; S : Y } → Y → P) → Y → P);
type Nat' = ∀P ({S : T(P); Z : T(P) → P } → T(P) → P);

fun x:Nat ↦ x:Nat';

let iter_nat : ∀P (Nat → P → (P → P) → P) =
  ∀P fun n a f ↦
    let delta : T(P) = fun p x ↦ f (p { Z = (fun x ↦ a); S = x } x) in
    n:Nat' {Z = fun x ↦ a; S = delta} delta;

#tests
let add : Nat → Nat → Nat = fun n m ↦ iter_nat n m succ;
let mul : Nat → Nat → Nat = fun n m ↦ iter_nat n 0 (add m);
let pred : Nat → Nat = fun n ↦ n { Z = 0; S = fun n ↦ n};
let sub : Nat → Nat → Nat = fun n m ↦ iter_nat m n pred;

#récurseur sans point fixe
type T(P) = ∀Y (( { Z : Y → Nat → P; S : Y } → Y → Nat → P) → Y → Nat → P);
type Nat' = ∀P ({S : T(P); Z : T(P) → Nat → P } → T(P) → Nat → P);

let rec_nat : ∀P (Nat → P → (Nat → P → P) → P) =
  ∀P fun n a f ↦
     let delta : T(P) = fun p x q ↦ f q (p { Z = (fun x p ↦ a); S = x } x (pred q)) in
     n:Nat' { Z = fun x p ↦ a; S = delta} delta n;

type F_Nat(K) = ∀X ({ Z : X ; S : K -> X} -> X);
type T(P) = ∀Y (( { Z : Y → P; S : Y } → Y → P) → Y → P);
type Nat' = ∀P ({S : T(P); Z : T(P) → P } → T(P) → P);

let fix_nat : ∀P (∀K ((K → P) → (F_Nat(K) → P)) → (Nat → P)) =
  ∀P fun f n  ↦
     let Z' : ∀Y (Y → P) =
           fun r ↦ f (fun x => x):(∀K K -> P) (\x.x.Z) in
     let S' : T(P) =
           fun p r ↦ f (fun s => p { Z = Z'; S = r } r) (\x.x.S p) in
     (n:Nat' { Z = Z'; S = S'}):(T(P) → P) S';

let 1 = succ 0;

let 2 = add 1 1;

let 4 = add 2 2;

let 8 = add 4 4;

let 64 = mul 8 8;

let bcp = mul 64 64;

let fact n = rec_nat n 1 mul;
