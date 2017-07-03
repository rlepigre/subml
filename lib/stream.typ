
type S(α,A) = να X {} → A × X
type Stream(A) = S(∞,A)

val map : ∀A ∀B (A → B) → ∀α S(α,A) → S(α,B) =
  fun f →
    let rec aux = fun s _ →
      let (a,s') = s {} in
      (f a, aux s')
    in aux

val coiter : ∀X∀A X → (X → A) → (X → X) → Stream(A) =
  fun s0 f n →
    let rec aux = fun x _ → (f x, aux (n x)) in
    aux s0

val rec group : ∀A Stream(A) → Stream(A×A) =
  fun s _ →
    let (a,s1) = s {} in
    let (b,s2) = s {} in
    ((a,b), group s2)