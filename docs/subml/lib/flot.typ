type Stream(A) = νX {} → A × X
type S(α,A) = να X {} → A × X

type RK(Y,X) = [ R of Y | K of X ]
type SF(α,β) = να X μβ Y {} → RK(Y,X)
type F = SF(∞,∞)
type UF = μ Y {} → RK(Y,F)
check F ⊂ UF
check UF ⊂ F

val rec[1] filter : ∀A UF → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

?val rec[1] filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

val rec[2] filter : ∀A F → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)


val consR : ∀α SF(α,∞) → SF(α,∞) = fun f _ → R f
val consK : ∀α SF(α,∞) → SF(α+1,∞) = fun f _ → K f

val rec[2] compose : UF → UF → F = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | K f1' → K (compose f1' f2')
            | R f1' → R (compose f1' f2'))
  | R f2' → R (compose f1 f2'))

(* Too slow
val rec 3 compose : F → F → F = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | K f1' → K (compose f1' f2')
            | R f1' → R (compose f1' f2'))
  | R f2' → R (compose f1 f2'))
*)

?val rec[2] compose : F → F → F = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose f1' f2')
            | K f1' → K (compose f1' f2'))
  | R f2' → R (compose f1 f2'))

type F2 = νX {} → μY [ R of Y | K of X ]
type UF2 = {} → μY [ R of Y | K of F2 ]
check F2 ⊂ UF2
check UF2 ⊂ F2
type SF2(α,β) = να X {} → μβ Y RK(Y,X)

val rec[1] filter2 : ∀A UF2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

val rec[2] filter2 : ∀A F2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

?val rec[1] filter2 : ∀A F2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

val rec[1] compose2 : UF2 → UF2 → F2 = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {}))

(* Too slow
val rec 3 compose2 : F2 → F2 → F2 = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {}))
*)

?val rec[2] compose2 : F2 → F2 → F2 = fun f1 f2 _ →
  (case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {}))

type F3 = νX μY [ R of Y | K of {} → X ]
type UF3 = μY [ R of Y | K of {} → F3 ]
check F3 ⊂ UF3
check UF3 ⊂ F3
check F2 ⊂ {} → F3
check {} → F3 ⊂ F2

val rec[1] filter3 : ∀A UF3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

val rec[2] filter3 : ∀A F3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

?val rec[1] filter3 : ∀A F3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

(*The following example fails, because in the
  typing of R (compose ...), the term is not normal
  and we therefore can not assume that the size of
  the stream is not zero.
*)
?val rec[1] compose3 : UF3 → UF3 → F3 = fun f1 f2 →
  (case f2 of
  | K f2' → (case f1 of
            | R f1' → R (compose3 f1' (f2' {}))
            | K f1' → K (fun _ → compose3 (f1' {}) (f2' {})))
  | R f2' → R (compose3 f1 f2'))

?val rec[2] compose3 : UF3 → UF3 → F3 = fun f1 f2 →
  (case f2 of
  | K f2' → (case f1 of
            | R f1' → R (compose3 f1' (f2' {}))
            | K f1' → K (fun _ → compose3 (f1' {}) (f2' {})))
  | R f2' → R (compose3 f1 f2'))

val compose3 : F3 → F3 → F3 = fun f1 f2 → compose2 (fun _ → f1) (fun _ → f2) {}

val rec[1] compose32 : UF3 → UF3 → F2 = fun f1 f2 _ →
  (case f2 of
  | K f2' → (case f1 of
            | R f1' → R (compose32 f1' (f2' {}) {})
            | K f1' → K (compose32 (f1' {}) (f2' {})))
  | R f2' → R (compose32 f1 f2' {}))

val compose3' : F3 → F3 → F3 = fun f1 f2 → compose32 f1 f2 {}

include "nat.typ"

val rec[1] filter_to_nat : UF → Stream(Nat) = fun s _ →
  (case s {} of
  | R s →
    let (n, r) = filter_to_nat s {} in (S n, r)
  | K s → (0, filter_to_nat s))

val rec[3] filter_to_nat : ∀α SF(α,∞) → S(α,Nat) = fun s _ →
  (case s {} of
  | R s →
    let (n, r) = filter_to_nat s {} in (S n, r)
  | K s → (0, filter_to_nat s))

val rec[1] nat_to_filter : Stream(Nat) → F = fun s _ →
  let (n, s) = s {} in
  let rec fn = fun n _ → case n of
  | Z → K (nat_to_filter s)
  | S p → R (fn p)
  in fn n {}

type UFS(α) = μ Y {} → RK(Y,SF(α,∞))

val rec[2] nat_to_filter : ∀α S(α,Nat) → SF(α,∞) = fun s _ →
  let (n, s) = s {} in
  let rec fn : ∀α SF(α,∞) → Nat → SF(α+1,∞) = fun s n → case n of
  | Z   → (fun _ → K s)
  | S p → (fun _ → R (fn s p))
  in fn (nat_to_filter s) n {}

val rec[1] filter2_to_nat : UF2 → Stream(Nat) = fun s _ →
  (case s {} of
  | R s →
    let (n, r) = filter2_to_nat (fun _ → s) {} in (S n, r)
  | K s → (0, filter2_to_nat s))

val rec[3] filter2_to_nat : ∀α SF2(α,∞) → S(α,Nat) = fun s _ →
  (case s {} of
  | R s →
    let (n, r) = filter2_to_nat (fun _ → s) {} in (S n, r)
  | K s → (0, filter2_to_nat s))

val rec[1] nat_to_filter2 : Stream(Nat) → F2 = fun s _ →
  let (n, s) = s {} in
  let rec fn = fun n → case n of
  | Z → K (nat_to_filter2 s)
  | S p → R (fn p)
  in fn n

val rec[2] nat_to_filter2 : ∀α S(α,Nat) → SF2(α,∞) = fun s _ →
  let (n, s) = s {} in
  let rec fn : ∀α SF2(α,∞) → Nat → SF2(α+1,∞) = fun s n _ → case n of
  | Z → K s
  | S p → R (fn s p {})
  in fn (nat_to_filter2 s) n {}
