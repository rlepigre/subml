type UNat = μX [Z  | S of X]

val rec print_unat : UNat → {} = fun n ↦
  case n of
  | Z  → print("Z\n")
  | S x → print("S"); print_unat x

val rec add : UNat → UNat → UNat = fun n m ↦
  case n of
  | Z  → m
  | S x → S(add x m)

val rec mul : UNat → UNat → UNat = fun n m ↦
  case n of
  | Z → Z
  | S x → add m (mul x m)

val rec compare : UNat → UNat → [Ls | Eq | Gt] = fun n m ↦
  case n of
  | Z   → (case m of Z → Eq | S m → Ls)
  | S n → (case m of Z → Gt | S m → compare n m)

val rec eq : UNat → UNat → [True | False] = fun n m ↦
  case compare n m of Eq → True | Ls → False | Gt → False

val rec leq : UNat → UNat → [True | False] = fun n m ↦
  case compare n m of Eq → True | Ls → True | Gt → False
