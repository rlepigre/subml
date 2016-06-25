type F(X) = {} → [ Z | S of X ]

type N' = μX F(X)

val rec idt : ∀o (μo X F(X)) → μo X F(X) = fun n ↦
  case n {} of
  | Z    → (fun u ↦ Z)
  | S[n] → (fun u ↦ S[idt n])
