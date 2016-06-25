include "advanced_lib/list.typ"
include "advanced_lib/nat.typ"

type T(A) = μX List(A × X)


val rec length : ∀A T(A) → Nat = fun t ↦
   case t of
   | []      → Z
   | Cons[c] → add (length c.hd.2) (length c.tl)

(*
type Key = μK [Atom of Nat | Pair of K × K ]
type Trie(A) = (μK ∃A [Nil | Branch of List(Nat × A) × (K with A = (K with A = A))]) with A = A

type A = [A]

check Trie(A) ⊂ [Nil | Branch of List(Nat × A) × Trie(Trie(A))]


val rec find : ∀B Trie(B) → Key → Option(B) =  fun t k ↦
  case t of
  | []       → None
  | Branch c →
    (case k of
     | Atom a → assoc (eq a) c.1
     | Pair p →
       let x = find c.2 p.1 in
       (case x of
       | None   → None
       | Some t → find t p.2))
*)
