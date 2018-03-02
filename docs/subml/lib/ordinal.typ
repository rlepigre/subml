include "nat.typ"

(* The santadard type for ordinals, semantics converges in 2^ω,
   even for Ord2, because |Ord| ⊂ Λ remains countable *)
type O(X) = μO.[ Z | S of O | L of X → O ]
type Ord  = O(Nat)
type Ord2 = O(Ord)

val rec add : ∀X.O(X) → O(X) → O(X) = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)
  | L f → L (fun q → add (f q) m)

(* A better definition for ordinals, semantics converges in 2^(2^ω).
   Not sur that in does not converge before. *)
type Ord0 = μO.[Z | S of O | L of ∃X.X → O]

check O(Ord) ⊂ Ord0
!check Ord0 ⊂ O(Ord)

check O(Ord0) ⊂ Ord0
!check Ord0 ⊂ O(Ord0)

(* still addition works for Ord0 *)
val rec add : Ord0 → Ord0 → Ord0 = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)
  | L f → L (fun q → add (f q) m)

(* A funny addition *)
val rec add0 : Ord0 → Ord0 → Ord0 = fun n m →
  case n of
  | Z   → m
  | S x → S(add0 x m)
  | L f → (case m of
          | Z → n
          | S y → S(add0 n y)
          | L g → L (fun z → add0 (f z.1) (g z.2)))

(* The same with type annotation *)
val rec add1 : Ord0 → Ord0 → Ord0 = fun n m →
  (case n of
  | Z   → m
  | S x → S(add1 x m)
  | L f →
  let X such that f : X → Ord0 in
  (case m of
  | Z → n
  | S y → S(add1 n y)
  | L g →
  let Y such that g : Y → Ord0 in
  L (fun (z:X×Y) → add1 (f z.1) (g z.2))))
