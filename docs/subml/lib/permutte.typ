type F(X) = [ Z | S of X]
type SN(α) = μα X.F(X)
type N = μX.F(X)

val rec add2 : ∀α.∀β.SN(α) → SN(β) → N = fun x y →
  case x of
  | Z   → y
  | S x → S(add2 y x)

val rec add3 : ∀α.∀β.∀γ.SN(α) → SN(β) → SN(γ) → N = fun x y z →
  case x of
  | Z   → add2 y z
  | S x → S(add3 y z x)

val rec add4 : ∀α.∀β.∀γ.∀δ.SN(α) → SN(β) → SN(γ) → SN(δ) → N = fun x y z t →
  case x of
  | Z   → add3 y z t
  | S x → S(add4 y z t x)
