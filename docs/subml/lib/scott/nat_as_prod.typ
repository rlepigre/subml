(* Unary natural with sums encoded using records *)

type Nat = μK ∀X { z : X ; s : K -> X ; …} -> X

val 0 : Nat = fun r → r.z
val succ : Nat → Nat = fun n r → r.s n

(* test du sous-typage *)
type Rel = μK ∀X { z : X ; s : K -> X ; p : K -> X; …} -> X

check Nat ⊂ Rel

(* Iterateur sans point fixe *)
type T(P) = ∀Y (( { z : Y → P; s : Y } → Y → P) → Y → P)
type Nat' = ∀P ({s : T(P); z : T(P) → P } → T(P) → P)

check Nat ⊂ Nat'

val iter_nat : ∀P (Nat → P → (P → P) → P) =
  fun n a f →
    let P such that _ : P in
    let delta : T(P) = fun p x → f (p { z = (fun x → a); s = x } x) in
    n:Nat' {z = (fun x → a); s = delta} delta

(* Tests *)
val add : Nat → Nat → Nat = fun n m → iter_nat n m succ
val mul : Nat → Nat → Nat = fun n m → iter_nat n 0 (add m)
val pred : Nat → Nat = fun n → n { z = 0; s = (fun n → n)}
val sub : Nat → Nat → Nat = fun n m → iter_nat m n pred

(* Récurseur sans point fixe *)
type T(P) = ∀Y (( { z : Y → Nat → P; s : Y } → Y → Nat → P) → Y → Nat → P)
type Nat' = ∀P ({s : T(P); z : T(P) → Nat → P } → T(P) → Nat → P)

check Nat ⊂ Nat'

val rec_nat : ∀P (Nat → P → (Nat → P → P) → P) =
  fun n a f →
     let P such that _ : P in
     let delta : T(P) = fun p x q → f q (p { z = (fun x p → a); s = x } x (pred q)) in
     n:Nat' { z = (fun x p → a); s = delta} delta n

type F_Nat(K) = ∀X { z : X ; s : K -> X} -> X
type T(P) = ∀Y ( { z : Y → P; s : Y } → Y → P) → Y → P
type Nat' = ∀P {s : T(P); z : T(P) → P } → T(P) → P

check Nat ⊂ Nat'

val fix_nat : ∀P (∀K (K → P) → F_Nat(K) → P) → Nat → P =
  fun f n →
     let P such that _ : P in
     let z' : ∀Y (Y → P) =
           fun r → f (fun x → x) (λx.x.z) in
     let s' : T(P) = (* FIXME: z = r below give an error on f above ??? *)
           fun p r → f (fun s → p { z = z'; s = r } r) (λx.x.s p) in
     n:Nat' { z = z'; s = s'} s'

val 1 = succ 0

val 2 = add 1 1

val 4 = add 2 2

val 8 = add 4 4

val 64 = mul 8 8

val bcp = mul 64 64

val fact : Nat → Nat = fun n → rec_nat n 1 mul

eval fact 4