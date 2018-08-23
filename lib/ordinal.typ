type Nat = μN.[Z | S of N]

(* Type of ordinals (parametrized by an index type). *)
type O(I) = μO.[Z | S of O | L of I → O]

(* We can define the addition function for every possible index type. *)
val rec o_add : ∀I.O(I) → O(I) → O(I) = fun o1 o2 →
  case o1 of
  | Z   → o2
  | S o → S (o_add o o2)
  | L f → L (fun x → o_add (f x) o2)

(* The standard type of ordinals (semantics converges at 2^ω). *)
type OrdN = O(Nat)

(* Other possible type of ordinals (also converges at 2^ω as |OrdN| ⊆ Λ). *)
type OrdO = O(OrdN)

(* Yet another definition (probably converges at 2^(2^ω), maybe before). *)
type OrdE = μO.[Z | S of O | L of ∃X.X → O]

(* Nat is a subtype of all the definitions. *)
check Nat  ⊆ OrdN
check Nat  ⊆ OrdO
check Nat  ⊆ OrdE

(* OrdO is a subtype of both OrdN and OrdE, and OrdN is a subtype of OrdE. *)
check OrdO ⊆ OrdN
check OrdO ⊆ OrdE
check OrdN ⊆ OrdE

!check OrdN ⊆ OrdO
!check OrdE ⊆ OrdN
!check OrdE ⊆ OrdO

(* Other subtyping checks. *)
check  O(OrdE) ⊆ OrdE
!check OrdE    ⊆ O(OrdE)

(* Still addition works for OrdE *)
val rec addE : OrdE → OrdE → OrdE = o_add

(* A funny addition, probably commutative. *)
val rec addE_c : OrdE → OrdE → OrdE = fun o1 o2 →
  case o1 of
  | Z    → o2
  | S o  → S (addE_c o o2)
  | L f1 → (case o2 of
            | Z    → o1
            | S o  → S (addE_c o1 o)
            | L f2 → L (fun z → addE_c (f1 z.1) (f2 z.2)))

(* The same with type annotation. *)
val rec addE_c : OrdE → OrdE → OrdE = fun o1 o2 →
  case o1 of
  | Z    → o2
  | S o  → S (addE_c o o2)
  | L f1 → let X1 such that f1 : X1 → OrdE in
           (case o2 of
            | Z    → o1
            | S o  → S (addE_c o1 o)
            | L f2 → let X2 such that f2 : X2 → OrdE in
                     L (fun (z:X1×X2) → addE_c (f1 z.1) (f2 z.2)))

(* Definition of the biggest ordinal. *)
val ordId : OrdE → OrdE = fun o → o
val big : OrdE = L ordId

eval big
eval addE_c big big
eval addE_c (S big) (S big)

(* Variants of the Burali-Forti paradox cannot break our normalization result
because SubML cannot encode comparision function on the OrdE representation of
the ordinals. *)
