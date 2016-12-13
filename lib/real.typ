include "lib/int.typ"

type D  = [P | Z | S ]
type I1 = νX {} → D × X
type IS(α) = να X {} → D × X

val d2i : D → Int = fun n →
  case n of
  | Z →  0
  | S →  1
  | P → n1

val dbl : Int → Int = fun n → add n n

val rec average' : ∀α Int → IS(α+1) → IS(α+1) → IS(α) = fun r a b _ →
  let (a0,a') = a {} in
  let (b0,b') = b {} in
  let d = add (dbl r) (add (d2i a0) (d2i b0)) in
  if even d then
    (sgn d, average' Z a' b')
  else
    let (a1,a'') = a' {} in
    let (b1,b'') = b' {} in
    let d = add (dbl d) (add (d2i a1) (d2i b1)) in
    let e = if      (ge d  2) then S
            else if (le d n2) then P
            else Z
    in
    let r' = sub d (dbl (d2i e)) in
    (e, average' r' a' b')

val average : ∀α IS(α+1) → IS(α+1) → IS(α) = average' Z

val oppD : D → D = fun a1 →
  case a1 of
  | Z → Z
  | S → P
  | P → S

val rec oppI : ∀α IS(α) → IS(α) = fun b _ →
  let (b0,b') = b {} in
  (oppD b0, oppI b')

val mulD : D → D → D = fun a1 b1 →
  case a1 of
  | Z → Z
  | S → b1
  | P → oppD b1

val rec mulDI : ∀α D → IS(α) → IS(α) = fun a1 b _ →
  let (b1,b') = b {} in
  (mulD a1 b1, mulDI a1 b')

val rec mulI : I1 → I1 → I1 =
   fun a b →
      let α such that _ : IS(α) in
      let (a0,a') = a {} in
      let (b0,b') = b {} in
      let (a1,a'') = a' {} in
      let (b1,b'') = b' {} in
      let q : IS(α+1) = fun _ → (mulD a0 b0,
                fun _ → (mulD a1 b0,
                  fun _ → (mulD a1 b1, mulI a'' b''))) in
      let p : IS(α+1) = average (fun _ → (mulD a0 b1, average (mulDI b1 a'') (mulDI a1 b'')))
                           (average (mulDI b0 a'') (mulDI a0 b'')) in
      average q p

val rec divI' : I1 → Pos → Int → I1 = fun a n s _ →
  let (a0, a') = a {} in
  let s' = add (dbl s) (d2i a0) in
  if geq s' n then
    (S, divI' a' n (sub s' n))
  else if leq s' (sub Z n) then
    (P, divI' a' n (add s' n))
  else (Z, divI' a' n s')

val divI : I1 → Pos → I1 = fun a n → divI' a n Z

type RS(α,β) = { m : IS(α); e : PS(β) }

include "lib/list.typ"

val rec extract : Pos → I1 → List(D) =
  fun n a → case n of
  | Z → []
  | S n → let (a0, a') = a {} in
          a0 :: extract n a'

val rec i0  : I1 = fun _ → (Z, i0)
val     i12 : I1 = fun _ → (S, i0)

val test16 = divI i12 3

eval extract 10  (mulI i0 i12)
eval extract 10  (mulI i12 i0)
eval extract 10  (mulI i12 i12)

eval extract 10  (mulI test16 i0)
eval extract 10  (mulI test16 i12)
eval extract 10  (mulI i0 test16)
eval extract 10  (mulI i12 test16)


eval extract 10 test16
eval extract 10 (average test16 test16)
eval extract 8  (mulI test16 test16)


(******************************************************************************)

type R = { m : I1; e : Pos }

val rec i0 : I1 = fun _ → (Z, i0)

val r0 : R = { m = i0;  e = Z   }
val r1 : R = { m = i12; e = S Z }

val opp : R → R = fun x → { m = oppI x.m; e = x.e }

val dbl : R → R =
  fun x →
    let (a0, a) = x.m {} in
    case a0 of
    | Z → { m = a; e = x.e }
    | S → (
      let (a1, a') = a {} in
      case a1 of
      | P → { m = (fun _ → (S, a')); e = x.e }
      | _ → { m = x.m; e = S x.e })
    | P → (
      let (a1, a') = a {} in
      case a1 of
      | S → { m = (fun _ → (P, a')); e = x.e }
      | _ → { m = x.m; e = S x.e })

val hlf : ∀α RS(∞,α+2) → RS(∞,α+1) =
  fun x →
    case x.e of
    | Z → { m = (fun _ → (Z,x.m)); e = Z }
    | S p → { m = x.m; e = p }

(*
val rec add : ∀α RS(∞,α+2) → RS(∞,α+2) → R = fun x y →
  let α such that x : RS(∞,α+2) in
  let { m = xm; e = xe } = x in
  let { m = ym; e = ye } = y in
  (case xe of
  | Z →
    (case ye of
    | Z → dbl { m = average xm ym; e = Z }
    | _ → dbl (add ((hlf (x:RS(∞,α+2))) : RS(∞,α)) (hlf y)))
  | _ → dbl (add (hlf x) (hlf y)))
*)