(* Binary coding of natural numbers using inductive types and native sums *)

type FBin(α) = μα K [ End | Zero of K | One of K ] (* allowed trailing zero *)
type Bin  = FBin(∞)
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

val times2 : ∀α FBin(α) → FBin(α+1) = fun x →
  case x of | End      → End
            | x        → Zero x

val rec pred : Bin → Bin = fun x →
  case x of
  | End    → End
  | One  n → times2 n
  | Zero n → One(pred n)

val rec is_zero : Bin → Bool = fun x →
  case x of
  | End    → tru
  | One _  → fls
  | Zero x → is_zero x

val rec complement : ∀α FBin(α) → FBin(α) = fun x →
  case x of
  | End    → End
  | One  x → Zero (complement x)
  | Zero x → One  (complement x)

val rec carryless_incr : ∀α FBin(α) → FBin(α) = fun x →
  case x of
  | End    → End
  | One  x → One (carryless_incr x)
  | Zero x → One x

val rec carryless_decr : ∀α FBin(α) → FBin(α) = fun x →
  case x of
  | End    → End
  | Zero x → (case x of End → Zero End | _ → One (carryless_decr x))
  | One  x → Zero x

val rec normalise : ∀α FBin(α) → FBin(α) = fun x →
  case x of
  | End    → End
  | One x  → One (normalise x)
  | Zero x → if is_zero x then End else Zero (normalise x)

type BitFun = [Z|O] → [Z|O] → [Z|O]

val rec bitmap : ∀α ([Z|O] → [Z|O]) → FBin(α) → FBin(α) = fun f x →
  case x of
  | End    → End
  | Zero x → (case f Z of
              | Z → Zero (bitmap f x)
              | O → One  (bitmap f x))
  | One  x →  (case f O of
              | Z → Zero (bitmap f x)
              | O → One  (bitmap f x))

(* FIXME should work with these type ? Need a max on ordinals ? *)
(* val rec bitwise : BitFun → ∀α FBin(α) → FBin(α) → FBin(α) = fun f x0 y0 → *)
(* val rec bitwise : ∀α BitFun → FBin(α) → FBin(α) → FBin(α) = fun f x0 y0 → *)
val rec bitwise : BitFun → Bin → Bin → Bin = fun f x0 y0 →
  let x0 = normalise x0 in
  let y0 = normalise y0 in
  let g = f Z in
  case x0 of
  | End    → bitmap g y0
  | Zero x → (case y0 of
              | End    → bitmap g x0
              | One y  → (case f Z O of
                          | Z → Zero (bitwise f x y)
                          | O → One  (bitwise f x y))
              | Zero y → (case f Z Z of
                          | Z → Zero (bitwise f x y)
                          | O → One  (bitwise f x y)))
  | One x  → (case y0 of
              | End    → bitmap g x0
              | One y  → (case f O O of
                          | Z → Zero (bitwise f x y)
                          | O → One  (bitwise f x y))
              | Zero y → (case f O Z of
                          | Z → Zero (bitwise f x y)
                          | O → One  (bitwise f x y)))

val land : Bin → Bin → Bin =
  bitwise (fun x y → case x of Z → Z | O → y)

val lor  : Bin → Bin → Bin =
  bitwise (fun x y → case x of O → O | Z → y)

val lxor : Bin → Bin → Bin =
  bitwise (fun x y → case x of O → (case y of Z → O | O → Z) | Z → y)

val eq_bin : Bin → Bin → Bool = fun x y →
  is_zero (lxor x y)

val rec land : Bin → Bin → Bin = fun x y →
  let x = normalise x in
  let y = normalise y in
  case x of
  | End    → End
  | One x  → (case y of
              | End    → End
              | One y  → One (land x y)
              | Zero y → Zero (land x y))
  | Zero x → (case y of
              | End → End
              | _   → Zero (land x y))

val rec lor : Bin → Bin → Bin = fun x y →
  let x = normalise x in
  let y = normalise y in
  case x of
  | End    → End : Bin
  | One x  → (case y of
              | End    → One x
              | One y  → One (lor x y)
              | Zero y → One (lor x y))
  | Zero x → (case y of
              | End    → Zero x
              | One y  → One (lor x y)
              | Zero y → Zero (lor x y))

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

val add_bin : Bin → Bin → Bin = add_aux Zero

type EBin = Option(Bin)
type EFBin(α) = Option(FBin(α))

val eOne : ∀α EFBin(α) → EFBin(α+1) = fun o → map_option (fun x → One x) o

val rec epred : ∀α FBin(α) → EFBin(α) =
fun x →
  case x of
  | End    → None
  | One n  → Some (times2 n)
  | Zero n → eOne (epred n)

val rec sub_aux : ∀α∀β Carry → FBin(α) → FBin(β) → EFBin(α) = fun c x y →
  case y of
  | End → (
    case c of
      Zero → Some x
    | One  → epred x)
  | Zero y' → (
    case x of
    | End → None
    | Zero x' → (
      case c of
      | Zero → map_option times2 (sub_aux Zero x' y')
      | One  → eOne (sub_aux One x' y'))
    | One x' → (
      case c of
      | Zero → eOne (sub_aux Zero x' y')
      | One  → map_option times2 (sub_aux Zero x' y')))
  | One y' → (
    case x of
    | End → None
    | Zero x' → (
      case c of
      | Zero → eOne (sub_aux One x' y')
      | One  → map_option times2 (sub_aux One x' y'))
    | One x' → (
      case c of
      | Zero → map_option times2 (sub_aux Zero x' y')
      | One  → eOne (sub_aux One x' y')))

val sub : ∀α∀β FBin(α) → FBin(β) → EFBin(α) = sub_aux Zero

val 20 = add_bin 10 10

val rec mul : Bin → Bin → Bin = fun x y →
  case x of
  | End     → 0
  | Zero x' → times2 (mul y x')
  | One  x' → add_bin y (times2 (mul y x'))

val 100 = mul 10 10

val rec divmod : Bin → Bin → Bin × Bin =
  fun x q →
    case x of
      End     → (End, End)
    | Zero x' → let r = divmod x' q in
                 (case sub (times2 r.2) q of
                    None → (times2 r.1, times2 r.2)
                  | Some x → (One r.1, x))
    | One x'  → let r = divmod x' q in (* x' = r.1 * q + r.2 ⇒ 2x'+ 1 = 2 r.1 q + 2 r.2 + 1  *)
                 (case (sub:Bin → Bin → EBin) (One r.2) q of (* FIXME *)
                    None → (times2 r.1, One r.2)
                  | Some x → (One r.1, x))

val div : Bin → Bin → Bin = fun x p → (divmod x p).1
val mod : Bin → Bin → Bin = fun x p → (divmod x p).2

val rec min_aux : ∀α∀β FBin(α) → FBin(β) → FBin(α) × Bool = fun x y →
  case x of
  | Zero x →
    (case y of
     | Zero y → let (z,b) = min_aux x y in (Zero z, b)
     | One y → let (z,b) = min_aux x y in ((if b then Zero z else One z), b)
     | End → (End, fls))
  | One x →
    (case y of
     | Zero y → let (z,b) = min_aux x y in ((if b then One z else Zero z), b)
     | One y → let (z,b) = min_aux x y in (One z, b)
     | End → (End, fls))
  | End → (End, tru)

val min : ∀α FBin(α) → FBin(α) → FBin(α) = fun x y → (min_aux x y).1

val rec gcd : Bin → Bin → EBin =
  fun x y →
    case x of
    | End →
      (case y of
      | End → None
      | y → Some y)
    | Zero x' →
      (case y of
      | End  → Some x
      | Zero y' → map_option times2 (gcd x' y')
      | One y' → gcd x' y)
    | One x' →
      (case y of
      | End  → Some x
      | One y' →
         (case sub x' y' of
         | None   →  bind_option (gcd x) (sub y' x')
         | Some z → gcd z y)
      | Zero y' → gcd x y')

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
*)
