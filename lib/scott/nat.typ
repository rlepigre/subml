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
    (fun p r ↦ f (p r (fun r ↦ a) r)):T(P)
    (fun r ↦ a)
    (fun p r ↦ f (p r (fun r ↦ a) r)):T(P)

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
     (fun p r q ↦ f q (p r (fun r q ↦ a) r (pred q))):T(P)
     (fun r q ↦ a)
     (fun p r q ↦ f q (p r (fun r q ↦ a) r (pred q))):T(P)
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
