(* A type for binary trees. *)
type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

(* A type for red-black trees. *)
type RBNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RBTree(A) = μX [Leaf | Node of RBNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RBTree({}) ⊆ Tree({})

(* Lookup function on simple binary trees. *)
val rec contains : ∀X (X → X → Cmp) → X → Tree(X) → Bool = fun cmp e t →
  case t of
  | Leaf    → fls
  | Node{value=v;left=l;right=r} →
     (case cmp e v of
      | Eq → tru
      | Ls → contains cmp e l
      | Gt → contains cmp e r)

(* The same function can be used on red-black trees. *)
val containsRB : ∀X (X → X → Cmp) → X → RBTree(X) → Bool =
  contains



(* Shortcut function to build a red-black tree node. *)
val node : ∀X X → [R | B] → RBTree(X) → RBTree(X) → RBNode(X, RBTree(X)) =
  fun e c l r → {value = e; color = c; left = l; right = r}

(* Color in black the root of a tree. If the strict subtrees of the input
   tree respect the invariants, then so does the output tree. *)
val blackRoot : ∀X RBTree(X) → RBTree(X) = fun t →
  case t of
  | Leaf                         → Leaf
  | Node{value=v;left=l;right=r} → Node(node v B l r)

(* Local balancing function. *)
val balance : ∀X RBNode(X, RBTree(X)) → RBTree(X) = fun n → Node n

val rec insert_aux : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t →
  case t of
  | Leaf    → Node(node e R Leaf Leaf)
  | Node{value=v;left=l;right=r;color=c} →
    (case cmp e v of
     | Eq → t
     | Ls → let l = insert_aux cmp e l in
            balance (node v c l r)
     | Gt → let r = insert_aux cmp e r in
            balance (node v c l r))

val insert : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t →
  blackRoot (insert_aux cmp e t)


include "nat.typ"
type NTree = RBTree(Nat)

val insert : Nat → NTree → NTree = insert compare

val test : NTree = insert (S Z) (insert Z (insert (S(S Z)) Leaf))
