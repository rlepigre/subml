type Nat = μX [Z  | S of X]

val rec print_nat : Nat → {} = fun n ↦
  case n of
  | Z    → print("Z\n")
  | S[x] → print("S"); print_nat x

val rec add : Nat → Nat → Nat = fun n m ↦
  case n of
  | Z    → m
  | S[x] → S[add x m]

val rec mul : Nat → Nat → Nat = fun n m ↦
  case n of
  | Z    → Z
  | S[x] → add m (mul x m)

val rec compare : Nat → Nat → Cmp = fun n m ↦
  case n of
  | Z    → (case m of Z → Eq | S[m] → Ls)
  | S[n] → (case m of Z → Gt | S[m] → compare n m)

val rec eq  : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → fls | Eq → tru | Gt → fls

val rec neq : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → tru | Eq → fls | Gt → tru

val rec ls  : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → tru | Eq → fls | Gt → fls

val rec leq : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → tru | Eq → tru | Gt → fls

val rec gt  : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → fls | Eq → fls | Gt → tru

val rec geq : Nat → Nat → Bool = fun n m ↦
  case compare n m of Ls → fls | Eq → tru | Gt → tru

val rec iter : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a ↦ case n of
  | Z    → a
  | S[p] → iter p f (f a)

val rec iter' : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a ↦ case n of
  | Z    → a
  | S[p] → f (iter' p f a)

val rec iter'' : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a ↦ case n of
  | Z    → a
  | S[p] → f (iter'' p f (f a))
