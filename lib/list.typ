include "lib/option.typ"

type List(A) = μX [Nil of {} | Cons of {head : A; tail : X}]

val head : ∀A (List(A) → Option(A)) = fun l ↦
  case l of
  | Nil[x]  → None[{}]
  | Cons[l] → Some[l.head]

val tail : ∀A (List(A) → Option(List(A))) = fun l ↦
  case l of
  | Nil[x]  → None[{}]
  | Cons[l] → Some[l.tail]

val map : ∀A ∀B ((A → B) → List(A) → List(B)) = fix fun r f l ↦
  case l of
  | Nil[x]  → Nil[{}]
  | Cons[l] → Cons[{head = f l.head; tail = r f l.tail;}]
