set verbose on

type UNat = μX [Z of {} | S of X]

val print_unat : UNat → {} = Y fun r n ↦
  case n of
  | Z[x] → print("Z\n"); {}
  | S[x] → print("S"); (r x)

val add : UNat → UNat → UNat = Y fun r n m ↦
  case n of
  | Z[x] → m
  | S[x] → S[r x m]

val mul : UNat → UNat → UNat = Y fun r n m ↦
  case n of
  | Z[x] → Z[x]
  | S[x] → add m (r x m)
