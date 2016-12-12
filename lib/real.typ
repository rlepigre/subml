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

val mulD : D → D → D = fun a1 b1 →
  case a1 of
  | Z → Z
  | S → b1
  | P → oppD b1

val rec mulDI : ∀α D → IS(α) → IS(α) = fun a1 b _ →
  let (b1,b') = b {} in
  (mulD a1 b1, mulDI a1 b')

(* fail termination, mainly because p is given type I1
   and average in the final call is given type I1 → I1 → I1
   loosing the type of q ... *)

?val rec mulI : I1 → I1 → I1 =
   fun a b →
      let (a0,a') = a {} in
      let (b0,b') = b {} in
      let (a1,a'') = a' {} in
      let (b1,b'') = b' {} in
      let q = fun _ → (mulD a0 b0,
                fun _ → (mulD a1 b0,
                  fun _ → (mulD a1 b1, mulI a'' b''))) in
      let p = average (fun _ → (mulD a0 b1, average (mulDI b1 a'') (mulDI a1 b'')))
                           (average (mulDI b0 a'') (mulDI a0 b'')) in
      average (fun _ → (mulD a0 b0,
                          (fun _ → (mulD a1 b0,
                           (fun _ → (mulD a1 b1, mulI a'' b'')))))) q
