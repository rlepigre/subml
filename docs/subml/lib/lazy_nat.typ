type F(X) = {} → [ Z | S of X ]

type N' = μX F(X)

val rec idt : ∀α (μα X F(X)) → μα X F(X) = fun n →
  case n {} of
  | Z   → fun u → Z
  | S n → fun u → S(idt n)
