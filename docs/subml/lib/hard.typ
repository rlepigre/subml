type Nat = μX [ Z | S of X ]
type FNat(α) = μα X [ Z | S of X ]

val rec add : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)

val rec f : ∀α ((FNat(α) → Nat) → Nat) → Nat =
  fun x → x (fun n →
    case n of
    | Z   → (Z:Nat)
    | S p → (f (fun g → x (fun q → add q (g p)))))

?val rec f : ((Nat → Nat) → Nat) → Nat =
  fun x → x (fun n →
    case n of
    | Z   → (Z:Nat)
    | S p → (f (fun g → x (fun q → add q (g p)))))

val f' : ((Nat → Nat) → Nat) → Nat = f

type SN(α) = μα X [ Z | S of X ]

val rec f' : ∀α ((SN(α) → Nat) → Nat) → Nat =
  let α such that _ : ((SN(α) → Nat) → Nat) → Nat in
  fun x → x (fun n →
    case (n:SN(α)) of
    | Z   → (Z:Nat)
    | S p → (f' (fun g → x (fun q → add q (g p)))))
