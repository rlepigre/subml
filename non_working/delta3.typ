type F = ∀X ∀Y (X → (X → X → Y) → Y)

(* In old prototypes, this example used to loop. This is not the case
   anymore because of compare implication with right first in this
   case *)

!check F ⊂ F -> F -> ∃X X

val g : F = λx y. y x x

val h = g g g
