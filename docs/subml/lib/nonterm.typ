type Stream(A) = νX {} → A × X
type F = νX {} → [ R of X | K of X ]

!val rec[2] filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

!val rec[3] filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

type Nat = μX [Z | S of X]

!val rec add : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x → add (S x) m

!val rec add : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x → add m (S x)

!val rec f : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x →
    (case m of
    | Z → Z
    | S y → f y (S (S x)))
