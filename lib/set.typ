(* A minimalist (and inefficient) set library implemented using (unbalanced)
   binary search trees. *)

type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

val rec mem : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → [True | False] =
  fun cmp e t ↦
    case t of
    | Leaf   → False
    | Node n →
       (case cmp e n.value of
        | Eq → True
        | Ls → mem cmp e n.left
        | Gt → mem cmp e n.right)

val rec add : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → Tree(X) =
  fun cmp e t ↦
    case t of
    | Leaf   → Node {value = e; left = Leaf; right = Leaf}
    | Node n →
       (case cmp e n.value of
        | Eq → t
        | Ls → let l = add cmp e n.left in
               Node {value = n.value; left = l; right = n.right}
        | Gt → let r = add cmp e n.right in
               Node {value = n.value; left = n.left; right = r})

val is_empty : ∀X Tree(X) → [True | False] = fun t ↦
  case t of
  | Leaf   → True
  | Node n → False

val singleton : ∀X X → Tree(X) = fun e ↦
  Node { value = e ; left = Leaf ; right = Leaf }

(* Interface of the set library. *)
type Ord(X) = {compare : X → X → [Ls | Eq | Gt]}
type Set(X) = ∃S
  { empty     : S
  ; is_empty  : S → [True | False]
  ; mem       : X → S → [True | False]
  ; add       : X → S → S
  ; singleton : X → S }

val makeSet : ∀X Ord(X) → Set(X) = ΛX fun o ↦
  { empty     : Tree(X)                      = Leaf
  ; is_empty  : Tree(X) → [True | False]     = is_empty
  ; mem       : X → Tree(X) → [True | False] = mem o.compare
  ; add       : X → Tree(X) → Tree(X)        = add o.compare
  ; singleton : X → Tree(X)                  = singleton }

(* Example use. *)
include "lib/unary.typ"
val ordNat : Ord(UNat) = {compare = compare}
val setNat : Set(UNat) = makeSet ordNat

val set012 : setNat.S =
  setNat.add (Z) (setNat.add (S Z) (setNat.add (S S Z) setNat.empty))
