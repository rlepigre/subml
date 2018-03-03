(* In old prototypes, this example used to loop. This is not the case
   anymore because we compare the right of implications first. *)

type F = ∀X.∀Y.X → (X → X → Y) → Y

val g : F = fun x y → y x x

!check F ⊆ F -> F -> ∃X.X
!val h = g g g
