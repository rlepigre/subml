(* A type for binary trees. *)
type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

(* A type for red-black trees. *)
type RBNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RBTree(A) = μX [Leaf | Node of RBNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RBTree({}) ⊆ Tree({})

(* Lookup function on simple binary trees. *)
val rec contains : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → [True | False] =
  fun cmp e t ↦
    case t of
    | Leaf   → False
    | Node n →
       (case cmp e n.value of
        | Eq → True
        | Ls → contains cmp e n.left
        | Gt → contains cmp e n.right)

(* The same function can be used on red-black trees. *)
val containsRB : ∀X (X → X → [Ls|Eq|Gt]) → X → RBTree(X) → [True | False] =
  contains
