
type NS(α) = μα X [Z | S of X]
type N = NS(∞)

val rec sub : ∀α∀β (NS(β+1)  → [S of NS(α)] → [ I of NS(α) | P of NS(β) ]) =
  fun n m →
    case m of
    | S m' →
      (case n of
      | Z → I Z
      | S n' →
        (case m' of
        | Z → P n'
        | S m'' →
          (case sub n' (S m'') of
           | I r → I (S r)
           | P d → P d)))


eval sub Z (S Z)
eval sub (S Z) (S Z)
eval sub (S (S Z)) (S Z)

eval sub Z (S (S Z))
eval sub (S Z) (S (S Z))
eval sub (S (S Z)) (S (S Z))
eval sub (S (S (S Z))) (S (S Z))


val rec mod : ∀α∀β N → [S of NS(α)] → NS(α) =
  fun n m →
    case sub n m of
    | I r → r
    | P n' →
      (case n' of
      | Z → Z
      | S n'' → mod (S n'') m)
(*
val rec gcd : N → N → N = fun n m →
  case n of
  | Z → m
  | S n' →
      (case n' of
      | Z → S Z
      | S n'' →
      (case m of
      | Z → n
      | S m' ->
         gcd (mod (S m') (S (S n''))) (S (S n''))))

val 0 = Z
val 1 = S 0
val 2 = S 1
val 3 = S 2
val 4 = S 3
val 5 = S 4
val 6 = S 5
val 7 = S 6
val 8 = S 7
val 9 = S 8
val 10 = S 9
val 11 = S 10
val 12 = S 11
val 13 = S 12

eval gcd 9 12
eval gcd 12 9*)