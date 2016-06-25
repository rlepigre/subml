(* A type for binary trees. *)
type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

(* A type for red-black trees. *)
type RBNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RBTree(A) = μX [Leaf | Node of RBNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RBTree({}) ⊆ Tree({})

(* Lookup function on simple binary trees. *)
val rec contains : ∀X (X → X → Cmp) → X → Tree(X) → Bool = fun cmp e t ↦
  case t of
  | Leaf    → fls
  | Node[n] →
     (case cmp e n.value of
      | Eq → tru
      | Ls → contains cmp e n.left
      | Gt → contains cmp e n.right)

(* The same function can be used on red-black trees. *)
val containsRB : ∀X (X → X → Cmp) → X → RBTree(X) → Bool =
  contains

val rec insert : ∀X (X → X → [Ls|Eq|Gt]) → X → Tree(X) → Tree(X) =
  fun cmp e t ↦
    case t of
    | Leaf    → Node[{value = e; left = Leaf; right = Leaf}]
    | Node[n] →
       (case cmp e n.value of
        | Eq → t
        | Ls → let l = insert cmp e n.left in
               Node[{value = n.value; left = l; right = n.right}]
        | Gt → let r = insert cmp e n.right in
               Node[{value = n.value; left = n.left; right = r}])

type Ord(X) = {compare : X → X → [Ls | Eq | Gt]}

type Set(E) = ∃S (* not the natural quantifier order … harder for the typing algorithm *)
  { empty : S
  ; add   : E → S → S
  ; mem   : E → S → Bool }

val makeSet : ∀X (Ord(X) -> Set(X)) = ΛX fun o ↦
  { empty : Tree(X)               = Leaf
  ; add   : X → Tree(X) → Tree(X) = insert o.compare
  ; mem   : X → Tree(X) → Bool    = contains o.compare }

include "advanced_lib/nat.typ"

val ordNat : Ord(Nat) = {compare = compare}
val setNat : Set(Nat) = makeSet ordNat

val emptyNat : setNat.S = setNat.empty

val singleton : Nat → setNat.S = fun n ↦
  setNat.add n emptyNat

(* Shortcut function to build a red-black tree node. *)
val node : ∀X X → [R | B] → RBTree(X) → RBTree(X) → RBNode(X, RBTree(X)) =
  fun e c l r ↦ {value = e; color = c; left = l; right = r}

(* Color in black the root of a tree. If the strict subtrees of the input
   tree respect the invariants, then so does the output tree. *)
val blackRoot : ∀X RBTree(X) → RBTree(X) = fun t ↦
  case t of
  | Leaf    → Leaf
  | Node[n] → Node[node n.value B n.left n.right]

(* Local balancing function. *)
val balance : ∀X RBNode(X, RBTree(X)) → RBTree(X) = fun n ↦
  n.left (* wont fix. *)

val rec insert_aux : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t ↦
  case t of
  | Leaf    → Node[node e R Leaf Leaf]
  | Node[n] →
    (case cmp e n.value of
     | Eq → t
     | Ls → let l = insert_aux cmp e n.left in
            balance (node n.value n.color l n.right)
     | Gt → let r = insert_aux cmp e n.right in
            balance (node n.value n.color n.left r))

val insert : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t ↦
  blackRoot (insert_aux cmp e t)


include "advanced_lib/nat.typ"
type NTree = RBTree(Nat)

val insert : Nat → NTree → NTree = insert compare

val test : NTree = insert S[Z] (insert Z (insert S[S[Z]] Leaf))
