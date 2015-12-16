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
