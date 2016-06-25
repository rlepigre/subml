(* List library. *)
include "advanced_lib/nat.typ"

type F(A,X) = [Nil of {} | Cons of {hd : A; tl : X}]
type List(A) = μX F(A,X)

val hd : ∀A List(A) → Option(A) = fun l ↦
  case l of
  | []      → None
  | Cons[l] → Some[l.hd]

val tl : ∀A (List(A) → Option(List(A))) = fun l ↦
  case l of
  | []      → None
  | Cons[l] → Some[l.tl]

val rec length : ∀A (List(A) → Nat) = fun l ↦
  case l of
  | []      → Z
  | Cons[x] → S[length x.tl]

val rec nth : ∀A (List(A) → Nat → Option(A)) = fun l n ↦
  case n of
  | Z    → hd l
  | S[x] → (case l of | [] → None | Cons[y] → nth y.tl x)

val rec map : ∀A ∀B ((A → B) → List(A) → List(B)) = fun f l ↦
  case l of
  | []      → []
  | Cons[l] → f l.hd :: map f l.tl

val rec append : ∀A (List(A) → List(A) → List(A)) = fun l1 l2 ↦
  case l1 of
  | []      → l2
  | Cons[l] → l.hd :: append l.tl l2

val rec concat : ∀A (List(List(A)) → List(A)) = fun l ↦
  case l of
  | []      → []
  | Cons[l] → append l.hd (concat l.tl)

val rec fold_left : ∀A ∀B ((B → A → B) → B → List(A) → B) = fun f e l ↦
  case l of
  | []      → e
  | Cons[l] → fold_left f (f e l.hd) l.tl

val rec assoc : ∀A ∀B (A → Bool) → List(A × B) → Option(B) = fun f l ↦
  case l of
  | []      → None
  | Cons[l] → if f (l.hd).1 then Some[(l.hd).2] else (assoc f l.tl)

val rec rev_append : ∀A List(A) → List(A) → List(A) = fun l1 l2 ↦
  case l1 of
  | [] → l2
  | Cons[l] → rev_append l.tl (l.hd :: l2)

val rev : ∀A List(A) → List(A) = fun l ↦ rev_append l []

val rec flatten : ∀A List(List(A)) → List(A) = fun l ↦
  case l of
  | [] → []
  | Cons[l] → rev_append (rev l.hd) (flatten l.tl)

(*
DOES NOT WORK, but this is expected:
  l'.tl and the content of l.tl do not agree on type,
  either typing fails, of termination fails

it would probably work if the definition of List (the outer one
was unroled … Lets try
val rec flatten2 : ∀A List(List(A)) → List(A) = fun l ↦
  case l of
  | [] → []
  | Cons l → (case l.hd of
    | [] → flatten2 l.tl
    | Cons l' → l'.hd :: flatten2 ((l'.tl) :: (l.tl)))
*)

val rec flatten2 : ∀A F(List(A),List(List(A))) → List(A) = fun l ↦
  case l of
  | []      → []
  | Cons[l] → (case l.hd of
               | []       → flatten2 l.tl
               | Cons[l'] → l'.hd :: flatten2 ((l'.tl) :: (l.tl)))

val flatten3 : ∀A List(List(A)) → List(A) = flatten2
