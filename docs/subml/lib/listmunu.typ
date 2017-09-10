include "list.typ"

type StreamS(α,A) = να X {} → A × X
type Stream(A) = StreamS(∞,A)
type T1S(α,A) = StreamS(α,List(A))
type T1(A) = T1S(∞,A)

type T2S(α,β,A) = να X {} → μβ Y [ Elt of A × Y | Next of X ]
type T2(A) = T2S(∞,∞,A)
type UT2S(α,β,γ,A) = μβ Y [ Elt of A × Y | Next of T2S(α,γ,A) ]
type UT2(A) = UT2S(∞,∞,∞,A)

(* TODO: writing the annotation is a bit too much *)
val rec t1_t2 : ∀A T1(A) → T2(A) = fun s _ →
  let α, A such that _ : UT2S(α,∞,∞,A) in
  let (l, s') = s {} in
  let rec f : List(A) →  UT2S(α,∞,∞,A) = fun l →
    case l of [] → Next(t1_t2 s')
            | x::l' → Elt(x,f l')
  in f l

val rec t2_t1' : ∀α∀β ∀A UT2S(α,β,∞,A) → T1S(α,A) = fun s _ →
  case s of
  | Elt (x,s) →
    let (l, s') = t2_t1' s {} in
    ((x::l), s')
  | Next(s) →
    ([], t2_t1' (s {}))

val t2_t1 : ∀α∀A T2S(α+1,∞,A) → T1S(α,A) = fun s → t2_t1' (s {})
