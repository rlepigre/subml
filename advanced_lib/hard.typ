type Nat = μX [ Z | S of X ]

val rec add : Nat → Nat → Nat = fun n m ↦
  case n of
  | Z    → m
  | S[x] → S[add x m]

val rec f : ((Nat → Nat) → Nat) → Nat =
  fun x ↦ x (fun n ↦
    case n of
    | Z    → (Z:Nat)
    | S[p] → (f (fun g ↦ x (fun q ↦ add q (g p)))))

val rec g : ∀o (((μo X [ Z | S of X ]) → Nat) → Nat) → Nat =
  Λo fun x ↦ x (fun n ↦
    case (n:μo X [ Z | S of X ]) of
    | Z    → (Z:Nat)
    | S[p] → (f (fun g ↦ x (fun q ↦ add q (g p)))))

(*
premier tour: n:Nat < Nat_a

p : Nat_b  (b < a)

g : Nat_b -> Nat

arg de f : (Nat_b -> Nat) -> Nat

Et donc c'est OK
*)

(*
val t = f (fun g ↦ g (g (S(S(S(Z))))))

iter Z g k = k
iter (S p) g k = S (iter p g (g k))

t = f (\g -> iter (g (S Z)) g (S (S Z)))

pr Z     = putStrLn "Z"
pr (S n) = putStr "S" >> pr n

main = pr t
*)
