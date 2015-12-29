(* A type for binary trees. *)
type SimpleNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SimpleNode(A,X)]

(* A type for red-black trees. *)
type RedBlackNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RedBlackTree(A) = μX [Leaf | Node of RedBlackNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RedBlackTree({}) ⊆ Tree({})


(* Binary search trees with integer keys. *)
include "lib/unary.typ"
type SearchTree = Tree(UNat)

val rec contains : SearchTree → UNat → [True | False] = fun t k ↦
  case t of
  | Leaf   → False
  | Node n →
     (case compare k n.value of
      | Eq → True
      | Ls → contains n.left  k
      | Gt → contains n.right k)

val rec insert : SearchTree → UNat → SearchTree = fun t k ↦
  case t of
  | Leaf   → Node {value = k; left = Leaf; right = Leaf}
  | Node n →
     (case compare k n.value of
      | Eq → t
      | Ls → Node {value = n.value; left = insert n.left k; right = n.right}
      | Gt → Node {value = n.value; left = n.left; right = insert n.right k})
