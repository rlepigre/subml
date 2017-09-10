

type A = [ A ]

type B = [ A ∪ B ]

val f : ∀X [ X ∪ A ] → [X ∪ B] = fun x →
  case x of A → B | x → x

(*
Not working yet:
- missing with syntax
- removal of fields would be better too (for pattern match,
  the dual is a cath all but some cases)

val g : ∀X ∀A ∀B (A → B) → { X ∩ a : A } → { X ∩ b : B } = fun r →
  { r without l with r = f l.a }
*)