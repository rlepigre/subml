(* Unary natural number library. *)
type Nat = μX [Z | S of X]

val pred : Nat → Nat = fun n →
  case n of
  | Z → Z
  | S x → x

val rec print_nat : Nat → {} = fun n →
  case n of
  | Z   → print("Z\n")
  | S x → print("S"); print_nat x

val rec add : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)

val rec mul : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → Z
  | S x → add m (mul x m)

val rec compare : Nat → Nat → Cmp = fun n m →
  case n of
  | Z   → (case m of Z → Eq | S _ → Ls)
  | S n → (case m of Z → Gt | S m → compare n m)

val eq  : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → fls | Eq → tru | Gt → fls

val neq : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → tru | Eq → fls | Gt → tru

val ls  : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → tru | Eq → fls | Gt → fls

val leq : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → tru | Eq → tru | Gt → fls

val gt  : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → fls | Eq → fls | Gt → tru

val geq : Nat → Nat → Bool = fun n m →
  case compare n m of Ls → fls | Eq → tru | Gt → tru

val rec iter : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a → case n of
  | Z    → a
  | S p  → iter p f (f a)

val rec iter' : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a → case n of
  | Z    → a
  | S p  → f (iter' p f a)

val rec iter'' : Nat → (Nat → Nat) → Nat → Nat =
  fun n f a → case n of
  | Z    → a
  | S p  → f (iter'' p f (f a))

val 0 : Nat = Z
val 1 : Nat = S 0
val 2 : Nat = S 1
val 3 : Nat = S 2
val 4 : Nat = S 3
val 5 : Nat = S 4
val 6 : Nat = S 5
val 7 : Nat = S 6
val 8 : Nat = S 7
val 9 : Nat = S 8
val 10 : Nat = S 9
