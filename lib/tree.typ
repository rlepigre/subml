(* A type for binary trees. *)
type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

(* A type for red-black trees. *)
type RBNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RBTree(A) = μX [Leaf | Node of RBNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RBTree({}) ⊆ Tree({})




val rec contains : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → [True | False] =
  fun cmp e t ↦
    case t of
    | Leaf   → False
    | Node n →
       (case cmp e n.value of
        | Eq → True
        | Ls → contains cmp e n.left
        | Gt → contains cmp e n.right)

val rec insert : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → Tree(X) =
  fun cmp e t ↦
    case t of
    | Leaf   → Node {value = e; left = Leaf; right = Leaf}
    | Node n →
       (case cmp e n.value of
        | Eq → t
        | Ls → let l = insert cmp e n.left in
               Node {value = n.value; left = l; right = n.right}
        | Gt → let r = insert cmp e n.right in
               Node {value = n.value; left = n.left; right = r})

type Ord = ∃X {compare : X → X → [Ls | Eq | Gt]}

type Set = ∃S ∃E
  { empty : S
  ; add   : E → S → S
  ; mem   : E → S → [True | False] }

val makeSet : Ord → Set = fun o ↦
  { empty : Tree(o.X)                        = Leaf
  ; add   : o.X → Tree(o.X) → Tree(o.X)      = insert o.compare
  ; mem   : o.X → Tree(o.X) → [True | False] = contains o.compare }

include "lib/unary.typ"

val ordNat : Ord = {compare = compare}
val setNat : Set = makeSet ordNat

val emptyNat : setNat.S = setNat.empty
