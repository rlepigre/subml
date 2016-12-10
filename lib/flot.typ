type Stream(A) = νX {} → A × X

type SF(α,β) = να X μβ Y {} → [ R of Y | K of X ]
type F = SF(∞,∞)

val rec 2 filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

?val rec filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

val rec 3 compose : F → F → F = fun f1 f2 →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → fun _ → R (compose f1' f2')
            | K f1' → fun _ → K (compose f1' f2'))
  | R f2' → fun _ → R (compose f1 f2'))

?val rec compose : F → F → F = fun f1 f2 →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → fun _ → R (compose f1' f2')
            | K f1' → fun _ → K (compose f1' f2'))
  | R f2' → fun _ → R (compose f1 f2'))

val rec 2 compose' : ∀α ∀β ∀γ SF(∞,α) → SF(∞,β) → SF(γ,∞) = fun f1 f2 →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → fun _ → R (compose' f1' f2')
            | K f1' → fun _ → K (compose' f1' f2'))
  | R f2' → fun _ → R (compose' f1 f2'))

?val rec compose' : ∀α ∀β ∀γ SF(∞,α) → SF(∞,β) → SF(γ,∞) = fun f1 f2 →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → fun _ → R (compose' f1' f2')
            | K f1' → fun _ → K (compose' f1' f2'))
  | R f2' → fun _ → R (compose' f1 f2'))

type F2 = νX {} →  μY [ R of Y | K of X ]

val rec 2 filter2 : ∀A F2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

?val rec filter2 : ∀A F2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

val rec 3 compose2 : F2 → F2 → F2 = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {}))

?val rec 2 compose2 : F2 → F2 → F2 = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {}))

(* The following example fail terminaison, not clear why *)
type F3 = νX μY [ R of Y | K of {} → X ]

val rec 2 filter3 : ∀A F3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

?val rec filter3 : ∀A F3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

?val rec 3 compose3 : F3 → F3 → F3 = fun f1 f2 →
  (case f2 of
  | K f2' → (case f1 of
            | R f1' → R (compose3 f1' (f2' {}))
            | K f1' → K (fun _ → compose3 (f1' {}) (f2' {})))
  | R f2' → R (compose3 f1 f2'))
