include "lib/unary.typ"

type List(A) = μX [Nil of {} | Cons of {hd : A; tl : X}]

val hd : ∀A (List(A) → Option(A)) = fun l ↦
  case l of
  | []    → None
  | Cons l → Some l.hd

val tl : ∀A (List(A) → Option(List(A))) = fun l ↦
  case l of
  | []    → None
  | Cons l → Some l.tl

val rec length : ∀A (List(A) → UNat) = fun l ↦
  case l of
  | []    → Z
  | Cons x → S(length x.tl)

val rec nth : ∀A (List(A) → UNat → Option(A)) = fun l n ↦
  case n of
  | Z → hd l
  | S x → (case l of | [] → None | Cons y → nth y.tl x)

val rec map : ∀A ∀B ((A → B) → List(A) → List(B)) = fun f l ↦
  case l of
  | []    → []
  | Cons l → f l.hd :: map f l.tl

val rec append : ∀A (List(A) → List(A) → List(A)) = fun l1 l2 ↦
  case l1 of
  | []    → l2
  | Cons l → l.hd :: append l.tl l2

val rec concat : ∀A (List(List(A)) → List(A)) = fun l ↦
  case l of
  | []    → []
  | Cons l → append l.hd (concat l.tl)

val rec fold_left : ∀A ∀B ((B → A → B) → B → List(A) → B) = fun f e l ↦
  case l of
  | []    → e
  | Cons l → fold_left f (f e l.hd) l.tl
