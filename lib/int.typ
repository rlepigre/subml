
type Pos = μX [Z | S of X]
type Neg = μX [Z | P of X]
type Int = [Z | S of Pos | P of Neg]
type PS(α) = μα X [Z | S of X]
type NS(α) = μα X [Z | P of X]

val 0 : Pos = Z
val 1 : Pos = S 0
val 2 : Pos = S 1
val 3 : Pos = S 2
val 4 : Pos = S 3
val 5 : Pos = S 4
val 6 : Pos = S 5
val 7 : Pos = S 6
val 8 : Pos = S 7
val 9 : Pos = S 8
val 10: Pos = S 9
val n0 : Neg = Z
val n1 : Neg = P n0
val n2 : Neg = P n1
val n3 : Neg = P n2
val n4 : Neg = P n3
val n5 : Neg = P n4
val n6 : Neg = P n5
val n7 : Neg = P n6
val n8 : Neg = P n7
val n9 : Neg = P n8
val n10: Neg = P n9

val rec suc : Int → Int = fun n →
  case n of
  | Z → S Z
  | S n → S (S n)
  | P n → n

val rec pre : Int → Int = fun n →
  case n of
  | Z → P Z
  | P n → P (P n)
  | S n → n

val rec 3 add : Int → Int → Int = fun n m →
  case n of
  | Z → m
  | S n → (case n of Z → suc m | S n → add n (suc (suc m)))
  | P n → (case n of Z → pre m | P n → add n (pre (pre m)))

?val rec 2 add : Int → Int → Int = fun n m →
  case n of
  | Z → m
  | S n → (case n of Z → suc m | S n → add n (suc (suc m)))
  | P n → (case n of Z → pre m | P n → add n (pre (pre m)))

?val rec 3 add : Int → Int → Int = fun n m →
  case n of
  | Z → m
  | S n → add n (suc m)
  | P n → add n (pre m)

val rec oppP : Pos → Neg = fun n →
  case n of
  | Z → Z
  | S p → P (oppP p)

val rec oppN : Neg → Pos = fun n →
  case n of
  | Z → Z
  | P p → S (oppN p)

val  opp : Int → Int = fun n →
  case n of
  | Z → Z
  | S p → P (oppP p)
  | P n → S (oppN n)

val rec sub : Int → Int → Int = fun n m →
  case n of
  | Z → opp m
  | S n → (case n of Z → suc (opp m) | S n → suc (suc (sub n m)))
  | P n → (case n of Z → pre (opp m) | P n → pre (pre (sub n m)))

eval print("0  : "); add n10 10
eval print("0  : "); sub 10 10
eval print("0  : "); sub n10 n10

eval print("15 : "); add 10 5
eval print("15 : "); add 5 10
eval print("-5 : "); add n10 5
eval print("-5 : "); add 5 n10
eval print("5  : "); add 10 n5
eval print("5  : "); add n5 10
eval print("-15: "); add n10 n5
eval print("-15: "); add n5 n10

eval print("5  : "); sub 10 5
eval print("-5 : "); sub 5 10
eval print("-15: "); sub n10 5
eval print("15 : "); sub 5 n10
eval print("15 : "); sub 10 n5
eval print("-15: "); sub n5 10
eval print("-5 : "); sub n10 n5
eval print("5  : "); sub n5 n10

val rec half : Int → Int = fun n →
  case n of
  | Z → Z
  | S n → (case n of Z → Z | S n → half n)
  | P n → (case n of Z → Z | P n → half n)

val rec even : Int → Bool = fun n →
  case n of
  | Z → tru
  | S n → (case n of Z → fls | S n → even n)
  | P n → (case n of Z → fls | P n → even n)

val odd = fun n → neg (even n)

val leq0 : Int → Bool = fun n →
  case n of
  | Z → tru | S _ → fls | P _ → tru

val le0 : Int → Bool = fun n →
  case n of
  | Z → fls | S _ → fls | P _ → tru

val geq0 : Int → Bool = fun n →
  case n of
  | Z → tru | S _ → tru | P _ → fls

val ge0 : Int → Bool = fun n →
  case n of
  | Z → fls | S _ → tru | P _ → fls

val leq : Int → Int → Bool = fun n m → leq0 (sub n m)
val le  : Int → Int → Bool = fun n m → le0  (sub n m)
val geq : Int → Int → Bool = fun n m → geq0 (sub n m)
val ge  : Int → Int → Bool = fun n m → ge0  (sub n m)

val sgn : Int → [ P | Z | S ] = fun n → case n of
  | Z → Z
  | S _ → S
  | P _ → P