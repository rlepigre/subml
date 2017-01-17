(* Examples from the paper "Set-Theoretic Types for Polymorphic Variants"
   (G. Castagna, T. Petrucciani and K. Nguyen) *)
val id : ∀X X → X = fun x → x

val ida = id A

val f = fun x →
  case x of
  | A → tru

val fida = f (id A)

val id2 = fun x →
  case x of
  | A → x
  | B → x

val id2a = id2 A

val g = fun x →
  case id2 x of
  | A → B
  | _ → x

(* The following needs to pass to obtain most general types. *)
?val test : [A | B] → [B] = fun x →
  case x of
  | A → B
  | _ → x

(* On possible fix is to add a syntactic sugar doing the following. *)
val test : [A | B] → [B] = fun x →
  case x of
  | A → let x = A in B
  | _ → let x = B in x
