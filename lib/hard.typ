type Nat = μX [ Z | S of X ]

val rec add : Nat → Nat → Nat = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)

val rec f : ((Nat → Nat) → Nat) → Nat =
  fun x → x (fun n →
    case n of
    | Z   → (Z:Nat)
    | S p → (f (fun g → x (fun q → add q (g p)))))

(*
val rec f' : ∀α (((μα X [ Z | S of X ]) → Nat) → Nat) → Nat =
  Λα fun x → x (fun n →
    case (n:μα X [ Z | S of X ]) of
    | Z   → (Z:Nat)
    | S p → (f' (fun g → x (fun q → add q (g p)))))
*)