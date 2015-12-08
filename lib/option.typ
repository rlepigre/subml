set verbose off

type Option(A) = [None of {} | Some of A]

val map_option : ∀X ∀Y ((X → Y) → Y → Option(X) → Y) = fun f d o ↦
  case o of
  | None[x] → d
  | Some[x] → f x
