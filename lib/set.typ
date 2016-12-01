(* A minimalist (and inefficient) set library implemented using (unbalanced)
   binary search trees. *)

type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

val rec mem : ∀X (X → X → Cmp) → X → Tree(X) → Bool =
  fun cmp e t →
    case t of
    | Leaf    → fls
    | Node{value=v;left=l;right=r} →
       (case cmp e v of
        | Eq → tru
        | Ls → mem cmp e l
        | Gt → mem cmp e r)

val rec add : ∀X (X → X → Cmp) → X → Tree(X) → Tree(X) = fun cmp e t →
  case t of
  | Leaf    → Node{value = e; left = Leaf; right = Leaf}
  | Node{value=v;left=l;right=r} →
     (case cmp e v of
      | Eq → t
      | Ls → let l = add cmp e l in
             Node{value = v; left = l; right = r}
      | Gt → let r = add cmp e r in
             Node{value = v; left = l; right = r})

val is_empty : ∀X Tree(X) → Bool = fun t →
  case t of
  | Leaf    → tru
  | Node n → fls

val singleton : ∀X X → Tree(X) = fun e →
  Node{ value = e ; left = Leaf ; right = Leaf }

(* Interface of the set library. *)
type Ord(X) = {compare : X → X → Cmp}
type Set(X) = ∃S
  { empty     : S
  ; is_empty  : S → Bool
  ; mem       : X → S → Bool
  ; add       : X → S → S
  ; singleton : X → S }

val makeSet : ∀X Ord(X) → Set(X) = ΛX fun o →
  { empty     : Tree(X)               = Leaf
  ; is_empty  : Tree(X) → Bool        = is_empty
  ; mem       : X → Tree(X) → Bool    = mem o.compare
  ; add       : X → Tree(X) → Tree(X) = add o.compare
  ; singleton : X → Tree(X)           = singleton }

(* Example use. *)
include "nat.typ"
val ordNat : Ord(Nat) = {compare = compare}

val setNat : Set(Nat) = makeSet ordNat

val set012 : setNat.S =
  setNat.add Z (setNat.add (S Z) (setNat.add (S (S Z)) setNat.empty))
