type Bool = [True | False]

(* Condition function. Prefer using built-in "if ... then ... else ...". *)
val cond : /\X Bool → X → X → X = fun c t e ↦
  case c of
  | True  → t
  | False → e

val or : Bool → Bool → Bool = fun a b ↦
  if a then True else b

val and : Bool → Bool → Bool = fun a b ↦
  if a then b else False
