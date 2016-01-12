include "lib/list.typ"
include "lib/nat.typ"

type T(A) = μX List(A × X)

val rec length : ∀A T(A) → Nat = fun t ↦
   case t of
   | []     → Z
   | Cons c → add (length c.hd.2) (length c.tl)

(*
type Key = μK [Atom of Nat | Pair of K × K ]
type Tree(A,X) = [Nil | Branch of List(Nat × A) × X]
type T2(A,T) = Tree(A,Tree(A,T))
type T(A) = μT T2(T2(A,T),T)

type A = [A]

check T(A) ⊂ Tree(A, μT T2(T2(A,Tree(A,T)),T))

check T(A) ⊂ [Nil | Branch of List(Nat × A) × T(T(A))]

val rec find : ∀A T(A) → Key → Option(A) = ΛA fun t k ↦
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