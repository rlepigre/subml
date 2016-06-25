(* Scott naturals. *)

(* The type of Scott naturals is encoded using an inductive type. *)
type FSNat(K) = ∀X (K → X) → X → X
type SNat = μK FSNat(K)

val z : SNat = fun f x ↦ x
val s : SNat → SNat = fun n f x ↦ f n

val zero  : SNat = z
val one   : SNat = s zero
val two   : SNat = s one
val three : SNat = s two
val four  : SNat = s three
val five  : SNat = s four
val six   : SNat = s five
val seven : SNat = s six
val eight : SNat = s seven
val nine  : SNat = s eight
val ten   : SNat = s nine

(* Constant time predecessor. *)
val pred : SNat → SNat = fun n ↦ n (fun p ↦ p) z

(* Iterator. *)
type U(P) = ∀Y Y → P
type T(P) = ∀Y (Y → U(P) → Y → P) → Y → P
type SNat' = ∀P T(P) → U(P) → T(P) → P

check SNat ⊂ SNat'

val iter : ∀P P → (P → P) → SNat → P = ΛP fun a f n ↦
  (n : SNat')
    ((fun p r ↦ f (p r ((fun r ↦ a) : (U(P))) r)) : (T(P)))
    ((fun r ↦ a) :  (U(P)))
    ((fun p r ↦ f (p r ((fun r ↦ a) : (U(P))) r)) : (T(P)))

(* Common functions. *)
val add : SNat → SNat → SNat = fun n m ↦ iter n s m
val mul : SNat → SNat → SNat = fun n m ↦ iter z (fun x ↦ add n x) m

val twenty : SNat = add ten ten
val thirty : SNat = mul six five

(* Equality function (using general recursion). *)
val rec eq : SNat → SNat → Bool = fun n m ↦
  n (fun np ↦ m (fun mp ↦ eq np mp) fls) (m (fun mp ↦ fls) tru)

(* Recursor. *)
type U(P) = ∀Y Y → SNat → P
type T(P) = ∀Y (Y → U(P) → Y → SNat → P) → Y → SNat → P

val recu : ∀P P → (SNat → P → P) → SNat → P = ΛP fun a f n ↦
  (n : ∀P T(P) → U(P) → T(P) → SNat → P)
     ((fun p r q ↦ f q (p r (fun r q ↦ a) r (pred q))) : (T(P)))
     ((fun r q ↦ a) : (U(P)))
     ((fun p r q ↦ f q (p r (fun r q ↦ a) r (pred q))) : (T(P)))
     (pred n)

(* Specialized fixpoint. *)
type G(P) = ∀K (K → P) → FSNat(K) → P
type U(P) = ∀K K → P
type T(P) = ∀K (K → U(P) → K → P) → K → P

val z' : FSNat(∀K K) = fun f x ↦ x
val s' : ∀K K → FSNat(K) = fun n f x ↦ f n

val zz : ∀P G(P) → U(P) = fun f r ↦ f (fun x ↦ x) z'
val sc : ∀P ∀K G(P) -> T(P) = fun f p r ↦
  f (fun s ↦ p r (zz f) r) (s' p)

val fixp : ∀P ∀K G(P) → SNat → P = ΛP fun f n ↦
  (n : ∀P T(P) → U(P) → T(P) → P) (sc f) (zz f) (sc f)


(* natural numbers using scott recursive encoding, typed *)
type F_Nat(K) = ∀X ((K → X) → X → X)
type Nat = μK F_Nat(K)


val z : Nat = fun f x ↦ x
val s : Nat → Nat = fun n f x ↦ f n
val pred : Nat → Nat = fun n ↦ (fun p ↦ p) z

type U(P) = ∀Y (Y → P)
type T(P) = ∀Y ((Y → U(P) → Y → P) → Y → P)
type Nat' = ∀P (T(P) → U(P) → T(P) → P)

check Nat ⊂ Nat'

val iter : ∀P P → (P → P) → Nat → P =
 ΛP fun (a:P) (f: P → P) (n:Nat) ↦
   (n:Nat')
     ((fun p r ↦ f (p r ((fun r ↦ a) : (U(P))) r)) : (T(P)))
     ((fun r   ↦ a)                             : (U(P)))
     ((fun p r ↦ f (p r ((fun r ↦ a) : (U(P))) r)) : (T(P)))
(*
type T(P) = ∀Y ((Y → P → P) → P);
let iter' = ∀P fun a:P f: (P → P) n:Nat ↦
 n:∀P (T(P) → P → P)
   ∀Y (fun p:(Y → P → P) ↦ f (p r a)) : T(P)
   a;
*)
(*
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
*)
(* fix f (S n) >
     (S n) (Sc f) (Z f) (Sc f) >
     (Sc f) n (Sc f) >
     f (n (Sc f) (Z f)) (S (Sc f)) >
     f (f ((P n) (Sc f) (Z f) *)
(*
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
*)