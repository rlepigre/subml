type Stream(A) = νX {} → A * X

type F(α,β) = να X μβ Y {} → [ R of Y | K of X ]

val rec 2 filter : ∀A F(∞,∞) → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

(* FIXME *)

val rec 3 compose : F(∞,∞) → F(∞,∞) → F(∞,∞) =
  fun f1 f2 →
    case f2 {} of
    | K f2' → (case f1 {} of
               | R f1' → fun _ → R (compose f1' f2')
               | K f1' → fun _ → K (compose f1' f2'))
    | R f2' → fun _ → R (compose f1 f2')

val rec 2 compose2 : ∀α ∀β ∀γ F(∞,α) → F(∞,β) → F(γ,∞) =
  fun f1 f2 →
    case f2 {} of
    | K f2' → (case f1 {} of
               | R f1' → fun _ → R (compose2 f1' f2')
               | K f1' → fun _ → K (compose2 f1' f2'))
    | R f2' → fun _ → R (compose2 f1 f2')


type G = νX μY [ R of Y | K of {} → X ]

?val rec 2 compose3 : G → G → G =
  fun f1 f2 →
    case f2 of
    | K f2' → (case f1 of
               | R f1' → R (compose3 f1' (f2' {}))
               | K f1' → K (fun _ → compose3 f1' f2'))
    | R f2' → R (compose3 f1 f2')
