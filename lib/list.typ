include "lib/option.typ"
include "lib/unary.typ"

type List(A) = μX [Nil of {} | Cons of {hd : A; tl : X}]

val hd : ∀A (List(A) → Option(A)) = fun l ↦
  case l of
  | Nil    → None
  | Cons l → Some l.hd

val tl : ∀A (List(A) → Option(List(A))) = fun l ↦
  case l of
  | Nil    → None
  | Cons l → Some l.tl

val length : ∀A (List(A) → UNat) = fix fun r l ↦
  case l of
  | Nil    → Z
  | Cons x → S(r x.tl)

val nth : ∀A (List(A) → UNat → Option(A)) = fix fun r l n ↦
  case n of
  | Z → hd l
  | S x → (case l of | Nil → None | Cons y → r y.tl x)

val map : ∀A ∀B ((A → B) → List(A) → List(B)) = fix fun r f l ↦
  case l of
  | Nil    → Nil
  | Cons l → Cons{hd = f l.hd; tl = r f l.tl }

val append : ∀A (List(A) → List(A) → List(A)) = fix fun r l1 l2 ↦
  case l1 of
  | Nil    → l2
  | Cons l → Cons{hd = l.hd; tl = r l.tl l2;}

val concat : ∀A (List(List(A)) → List(A)) = fix fun r l ↦
  case l of
  | Nil    → Nil
  | Cons l → append l.hd (r l.tl)

val fold_left : ∀A ∀B ((B → A → B) → B → List(A) → B) = fix fun r f e l ↦
  case l of
  | Nil    → e
  | Cons l → r f (f e l.hd) l.tl
