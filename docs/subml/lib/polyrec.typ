include "list.typ"
include "nat.typ"

type T(A) = μX.List(A × X)

val rec length : ∀A.T(A) → Nat = fun t →
   case t of
   | []   → Z
   | x::l → add (length x.2) (length l)

(*
type Key = μK.[Atom of Nat | Pair of K × K ]
type Trie(A) = (μK.∃A.[Nil | Branch of List(Nat × A) × (K with A = (K with A = A))]) with A = A
type A = [A]

check Trie(A) ⊂ [Nil | Branch of List(Nat × A) × Trie(Trie(A))]

val rec find : ∀A.T(A) → Key → Option(A) = ΛA fun t k →
  case t of
  | []       → None
  | Branch c →
    (case k of
     | Atom a → assoc (eq a) (c.1 : List(Nat × A))
     | Pair p →
       let x = find (c.2:T(T(A))) p.1 in
       (case x of
       | None   → None
       | Some t → find (t:T(A)) p.2))
*)
