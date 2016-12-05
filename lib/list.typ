(* List library. *)
include "nat.typ"

type SList(α,A) = μα X [Nil of {} | Cons of {hd : A; tl : X}]
type List(A) = SList(∞,A)

val cons : ∀A A → List(A) → List(A) = fun e l → e::l

val nil : ∀A List(A) = Nil

val hd : ∀A List(A) → Option(A) = fun l →
  case l of
  | []   → None
  | x::l → Some x

val tl : ∀A ∀α (SList(α+1,A) → Option(SList(α,A))) = fun l →
  case l of
  | []   → None
  | x::l → Some l

(* Check that the above type is general enough *)
val tl' : ∀A (List(A) → Option(List(A))) = tl

val rec length : ∀A (List(A) → Nat) = fun l →
  case l of
  | []   → Z
  | x::l → S(length l)

val rec nth : ∀A (List(A) → Nat → Option(A)) = fun l n →
  case n of
  | Z   → hd l
  | S x → (case l of [] → None | a::l → nth l x)

val rec map : ∀A ∀B ∀α ((A → B) → SList(α,A) → SList(α,B)) = fun f l →
  case l of
  | []   → []
  | x::l → f x :: map f l

(* Check that the above type is general enough *)
val map' : ∀A ∀B ((A → B) → List(A) → List(B)) = map

val rec append : ∀A (List(A) → List(A) → List(A)) = fun l1 l2 →
  case l1 of
  | []   → l2
  | x::l → x :: append l l2

val rec concat : ∀A (List(List(A)) → List(A)) = fun l →
  case l of
  | []      → []
  | x::l → append x (concat l)

val rec fold_left : ∀A ∀B ((B → A → B) → B → List(A) → B) = fun f e l →
  case l of
  | []      → e
  | x::l → fold_left f (f e x) l

val rec assoc : ∀A ∀B (A → Bool) → List(A × B) → Option(B) = fun f l →
  case l of
  | []      → None
  | x::l → if f x.1 then Some x.2 else (assoc f l)

val rec rev_append : ∀A List(A) → List(A) → List(A) = fun l1 l2 →
  case l1 of
  | [] → l2
  | x::l → rev_append l (x :: l2)

val rev : ∀A List(A) → List(A) = fun l → rev_append l []

val rec flatten : ∀A List(List(A)) → List(A) = fun l →
  case l of
  | [] → []
  | x::l → rev_append (rev x) (flatten l)

val rec flatten2 : ∀A List(List(A)) → List(A) = fun ll →
  case ll of
  | [] → []
  | l::ll → (case l of
    | [] → flatten2 ll
    | x::l → x :: flatten2 (l :: ll))