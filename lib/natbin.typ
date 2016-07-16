(* Binary coding of natural numbers using inductive types and native sums *)

type Bin  = μK [ End | Zero of K | One of K ] (* allowed trailing zero *)
type EBin = [ Error | End | Zero of Bin | One of Bin ]
type RBin = [ Minus of Bin | End | Zero of Bin | One of Bin ] (*relative numbers*)


val rec succ : Bin → Bin = fun x →
  case x of
  | End    → One End
  | One n  → Zero(succ n)
  | Zero n → One n

val 0  : Bin = End
val 1  : Bin = succ 0
val 2  : Bin = succ 1
val 3  : Bin = succ 2
val 4  : Bin = succ 3
val 5  : Bin = succ 4
val 6  : Bin = succ 5
val 7  : Bin = succ 6
val 8  : Bin = succ 7
val 9  : Bin = succ 8
val 10 : Bin = succ 9

val times2 : Bin → Bin = fun x →
  case x of | End      → End
            | x        → Zero x

val rec pred : Bin → Bin = fun x →
  case x of
  | End    → End
  | One  n → times2 n
  | Zero n → One(pred n)

val opp : RBin → RBin = fun x →
  case x of
    End     → End
  | Minus n → n
  | n       → Minus(n)

val rsucc : RBin → RBin = fun x →
  case x of
  | Minus n → opp (pred n)
  | End     → 1
  | n       → succ n

val rpred : RBin → RBin = fun x →
  case x of
  | Minus n → opp (succ n)
  | End     → Minus 1
  | n       → pred n

type Carry = [Zero | One]

val add_carry : Carry → Bin → Bin = fun c x →
  case c of | One → succ x | Zero → x

val rec add_aux : Carry → Bin → Bin → Bin = fun c x y →
  case x of
  | End     → add_carry c y
  | One x' → (
    case y of
    | End     → add_carry c x
    | One y'  → (
        case c of
        | Zero → times2 (add_aux (One:Carry) x' y')
        | One → One(add_aux (One:Carry) x' y'))
    | Zero y' → (
        case c of
        | Zero → One(add_aux (Zero:Carry) x' y')
        | One  → times2 (add_aux (One:Carry) x' y')))
  | Zero x' → (
    case y of
    | End     → add_carry c x
    | One y'  → (
        case c of
        | Zero → One(add_aux (Zero:Carry) x' y')
        | One  → times2 (add_aux (One:Carry) x' y'))
    | Zero y' → (
        case c of
        | Zero → times2 (add_aux (Zero:Carry) x' y')
        | One  → One(add_aux (Zero:Carry) x' y')))

val add : Bin → Bin → Bin = add_aux Zero

val catch : (Bin → EBin) → EBin → EBin =
  fun f x → case x of Error → Error | End → f End | Zero x → f (Zero x) | One x → f (One x)

val eOne : EBin → EBin =
  fun x → case x of Error → Error | End → One End | Zero x → One (Zero x) | One x → One (One x)

val epred : Bin → EBin =
fun x →
  case x of
  | End    → Error
  | One n  → times2 n
  | Zero n → eOne (pred n)

val rec sub_aux : Carry → Bin → Bin → EBin = fun c x y →
  case y of
  | End → (
    case c of
      Zero → x
    | One  → epred x)
  | Zero y' → (
    case x of
    | End → Error
    | Zero x' → (
      case c of
      | Zero → catch times2 (sub_aux Zero x' y')
      | One  → eOne (sub_aux One x' y'))
    | One x' → (
      case c of
      | Zero → eOne (sub_aux Zero x' y')
      | One  → catch times2 (sub_aux Zero x' y')))
  | One y' → (
    case x of
    | End → Error
    | Zero x' → (
      case c of
      | Zero → eOne (sub_aux One x' y')
      | One  → catch times2 (sub_aux One x' y'))
    | One x' → (
      case c of
      | Zero → catch times2 (sub_aux Zero x' y')
      | One  → eOne (sub_aux One x' y')))

val sub = sub_aux Zero

val 20 = add 10 10

val rec 3 mul : Bin → Bin → Bin = fun x y →
  case x of
  | End     → 0
  | Zero x' → times2 (mul y x')
  | One  x' → add y (times2 (mul y x'))

val 100 = mul 10 10

val rec divmod : Bin → Bin → Bin × Bin =
  fun x q →
    case x of
      End     → (End, End)
    | Zero x' → let r = divmod x' q in
                 (case sub (times2 r.2) q of
                    Error → (times2 r.1, times2 r.2)
                  | x → (One r.1, x))
    | One x'  → let r = divmod x' q in (* x' = r.1 * q + r.2 ⇒ 2x'+ 1 = 2 r.1 q + 2 r.2 + 1  *)
                 (case sub (One r.2) q of
                    Error → (times2 r.1, One r.2)
                  | x → (One r.1, x))

val div : Bin → Bin → Bin = fun x p → (divmod x p).1
val mod : Bin → Bin → Bin = fun x p → (divmod x p).2

(*
Termination of the following functions fails

val rec decimalPrint : Bin → {} =
  fun x →
    let r = divmod x 10 in
    (case r.1 of End → {} | z →
     decimalPrint r.1) (case r.2 of
      End → print("0")
    | One r → (* 1 3 5 7 9 *)
      (case r of
        End → print("1")
      | One r → (* 3 7 *)
        (case r of
          End → print("3")
        | x → print("7"))
      | Zero r → (* 5 9 *)
        (case r of
          Zero r → print("9")
        | One r → print("5"))
      )
    | Zero r → (* 2 4 6 8 *)
      (case r of
        One r → (* 2 6 *)
        (case r of
          End → print("2")
        | x → print("6"))
      | Zero r → (* 4 8 *)
        (case r of
          Zero r → print("8")
        | One r → print("4"))
      ))

val rec fact : Bin → Bin = fun x →
  case x of
  | End → 1
  | x:Bin' → mul x (fact (pred x))

val test = fact 20


val rec gcd : Bin → Bin → EBin =
  fun x y →
    case x of
      End →
      (case y of
        End → Error
      | y → y)
    | Zero x' →
      (case y of
        End  → x
      | Zero y' → catch times2 (gcd x' y')
      | One y → gcd x' (One y))
    | One x' →
      (case y of
        End  → x
      | One y' →
         (case sub x' y' of
           Error → catch (gcd x) (sub y' x')
         | z → gcd y z)
      | Zero y' → gcd x y')
*)