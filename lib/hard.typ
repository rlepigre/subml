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

(* FIXME: ordinal indication fails for recursive function
val f' : ∀α (((μα X [ Z | S of X ]) → Nat) → Nat) → Nat =
  Λα fix f' → fun x → x (fun n →
    case (n:μα X [ Z | S of X ]) of
    | Z   → (Z:Nat)
    | S p → (f' (fun g → x (fun q → add q (g p)))))
*)