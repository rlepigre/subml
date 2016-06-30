(* Binary coding of natural numbers using inductive types and native sums *)

# boolean are needed
include "bool.typ";

# recursive definition are used and this a typed file
recursive; typed; inductive;

# Binary representation with lower bits first and no trailing Zero
type BinAux(A) = μK [ One of A | Zero of K ];
type Bin = μK [ End | Zero of BinAux(K) | One of K ]; (* natural *)
type Bin' = BinAux(Bin); (* non zero naturals *)
type EBin = [ Error ∪ Bin ];
type RBin = [ Minus of Bin' ∪ Bin ];

fun x:Bin' ↦ x:Bin;
fun x:Bin ↦ x:EBin;
fun x:Bin ↦ x:RBin;
untyped fun x:Bin ↦ x:Bin';

let rec succ : Bin → Bin' = fun x ↦
  case x of
  | End[] ↦ One[End[]]
  | One[n] ↦ Zero[succ n]
  | Zero[n] ↦ One[n]
;

let 0 : Bin = End[];
let 1 : Bin' = succ 0;
let 2 : Bin' = succ 1;
let 3 : Bin' = succ 2;
let 4 : Bin' = succ 3;
let 5 : Bin' = succ 4;
let 6 : Bin' = succ 5;
let 7 : Bin' = succ 6;
let 8 : Bin' = succ 7;
let 9 : Bin' = succ 8;
let 10 : Bin' = succ 9;

let times2 : Bin → Bin = fun x ↦
  case x of | End[] ↦ End[]
            | x ↦ Zero[x]
;

let rec pred : Bin' → Bin = fun x ↦
  case x of
  | One[n] ↦ times2 n
  | Zero[n] ↦ One[pred n];

let opp : RBin → RBin = fun x ↦
  case x of
    End[] ↦ End[]
  | Minus[n] ↦ n
  | n ↦ Minus[n];

let rsucc : RBin → RBin = fun x ↦
  case x of
    Minus[n] ↦ opp (pred n)
  | n ↦ succ n;

let rpred : RBin → RBin = fun x ↦
  case x of
    Minus[n] ↦ Minus[succ n]
  | End[] ↦ Minus[1]
  | n ↦ pred n;

let catch : (Bin → EBin) → EBin → EBin =
  fun f x ↦ case x of Error[] ↦ Error[] | x ↦ f x;

let eOne : EBin → EBin =
  fun x ↦ case x of Error[] ↦ Error[] | x ↦ One[x];

let epred : Bin → EBin =
fun x ↦
  case x of
  | End[] ↦ Error[]
  | One[n] ↦ times2 n
  | Zero[n] ↦ eOne (pred n);

type Carry = [Zero | One];

let add_carry : Carry → Bin → Bin = fun c x ↦
  case c of | One[] ↦ succ x | Zero[] ↦ x;

let rec add_aux : Carry → Bin → Bin → Bin = fun c x y ↦
  case x of
  | End[] ↦ add_carry c y
  | Zero[x'] ↦ (
    case y of
    | End[] ↦ add_carry c x
    | Zero[y'] ↦ (
      case c of
      | Zero[] ↦ times2 (add_aux Zero[] x' y')
      | One[] ↦ One[add_aux Zero[] x' y'])
    | One[y'] ↦ (
      case c of
      | Zero[] ↦ One[add_aux Zero[] x' y']
      | One[] ↦ times2 (add_aux One[] x' y')))
  | One[x'] ↦ (
    case y of
    | End[] ↦ add_carry c x
    | Zero[y'] ↦ (
      case c of
      | Zero[] ↦ One[add_aux Zero[] x' y']
      | One[] ↦ times2 (add_aux One[] x' y'))
    | One[y'] ↦ (
      case c of
      | Zero[] ↦ times2 (add_aux One[] x' y')
      | One[] ↦ One[add_aux One[] x' y']));

let add = add_aux Zero[];

let rec sub_aux : Carry → Bin → Bin → EBin = fun c x y ↦
  case y of
  | End[] ↦ (
    case c of
      Zero[] ↦ x
    | One[] ↦ epred x)
  | Zero[y'] ↦ (
    case x of
    | End[] ↦ Error[]
    | Zero[x'] ↦ (
      case c of
      | Zero[] ↦ catch times2 (sub_aux Zero[] x' y')
      | One[] ↦ eOne (sub_aux One[] x' y'))
    | One[x'] ↦ (
      case c of
      | Zero[] ↦ eOne (sub_aux Zero[] x' y')
      | One[] ↦ catch times2 (sub_aux Zero[] x' y')))
  | One[y'] ↦ (
    case x of
    | End[] ↦ Error[]
    | Zero[x'] ↦ (
      case c of
      | Zero[] ↦ eOne (sub_aux One[] x' y')
      | One[] ↦ catch times2 (sub_aux One[] x' y'))
    | One[x'] ↦ (
      case c of
      | Zero[] ↦ catch times2 (sub_aux Zero[] x' y')
      | One[] ↦ eOne (sub_aux One[] x' y')));

let sub = sub_aux Zero[];

let 20 = add 10 10;

let rec mul : Bin → Bin → Bin = fun x y ↦
  case x of
  | End[] ↦ 0
  | Zero[x'] ↦ times2 (mul y x')
  | One[x'] ↦ add y (times2 (mul y x'));

let 100 = mul 10 10;

let rec divmod : Bin → Bin' → Bin × Bin =
  fun x q ↦
    case x of
      End[] ↦ (End[], End[])
    | Zero[x'] ↦ let r = divmod x' q in
                 (case sub (times2 r.2) q of
		    Error[] ↦ (times2 r.1, times2 r.2)
		  | r' ↦ (One[r.1], r'))
    | One[x'] ↦ let r = divmod x' q in (* x' = r.1 * q + r.2 ⇒ 2x'+ 1 = 2 r.1 q + 2 r.2 + 1  *)
                 (case sub (One[r.2]) q of
		    Error[] ↦ (times2 r.1, One[r.2])
		  | r' ↦ (One[r.1], r'));

let div : Bin → Bin' → Bin = fun x p ↦ (divmod x p).1;
let mod : Bin → Bin' → Bin = fun x p ↦ (divmod x p).2;

let rec decimalPrint : Bin → ∀X (X → X) =
  fun x ↦
    let r = divmod x 10 in
    (case r.1 of End[] ↦ "" | z ↦
     decimalPrint r.1) (case r.2 of
      End[] ↦ "0"
    | One[r] ↦ (* 1 3 5 7 9 *)
      (case r of
        End[] ↦ "1"
      | One[r] ↦ (* 3 7 *)
	(case r of
	  End[] ↦ "3"
	| x ↦ "7")
      | Zero[r] ↦ (* 5 9 *)
        (case r of
	  Zero[r] ↦ "9"
	| One[r] ↦ "5")
      )
    | Zero[r] ↦ (* 2 4 6 8 *)
      (case r of
        One[r] ↦ (* 2 6 *)
	(case r of
	  End[] ↦ "2"
	| x ↦ "6")
      | Zero[r] ↦ (* 4 8 *)
        (case r of
	  Zero[r] ↦ "8"
	| One[r] ↦ "4")
      ));

let rec fact : Bin → Bin = fun x ↦
  case x of
  | End[] ↦ 1
  | x:Bin' ↦ mul x (fact (pred x));

let test = fact 20;


let rec gcd : Bin → Bin → EBin =
  fun x y ↦
    case x of
      End[] ↦
      (case y of
        End[] ↦ Error[]
      | y ↦ y)
    | Zero[x'] ↦
      (case y of
        End[] ↦ x
      | Zero[y'] ↦ catch times2 (gcd x' y')
      | y ↦ gcd x' y)
    | One[x'] ↦
      (case y of
        End[] ↦ x
      | One[y'] ↦
         (case sub x' y' of
	   Error[] ↦ catch (gcd x) (sub y' x')
	 | z ↦ gcd y z)
      | Zero[y'] ↦ gcd x y');
