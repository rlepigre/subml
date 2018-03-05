(* Type of streams. *)
type SStream(α,A) = να X.{} → A × X
type Stream(A) = SStream(∞,A)

(* Type of filter on stream with constructors [R]eject and [K]eep. Note that
   [K] must appear infinitely many times. *)
type SFilter(α,β) = να X.μβ Y.{} → [R of Y | K of X]
type Filter = SFilter(∞,∞)

(* Unfolded variant of [Filter] (helps the termination checker). *)
type UFilter = μ Y.{} → [R of Y | K of Filter]
check Filter  ⊆ UFilter
check UFilter ⊆ Filter

(* Apply a [UFilter] to a stream. *)
val rec[1] filter : ∀A.UFilter → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

(* The same fails if we use a [Filter]. *)
?val rec[1] filter : ∀A.Filter → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

(* Except if we unroll the fixpoint twice. *)
val rec[2] filter : ∀A.Filter → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter f' tl
    | K f' → fun _ → (hd, filter f' tl)

(* Constructor for filters. *)
val consR : ∀α.SFilter(α,∞) → SFilter(α,∞)   = fun f _ → R f
val consK : ∀α.SFilter(α,∞) → SFilter(α+1,∞) = fun f _ → K f

(* Composition of filters ([UFilter] need two unrollings). *)
val rec[2] compose : UFilter → UFilter → Filter = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | K f1' → K (compose f1' f2')
            | R f1' → R (compose f1' f2'))
  | R f2' → R (compose f1 f2')

(* The same with [Filter] needs three unrollings. *)
val rec[3] compose : Filter → Filter → Filter = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | K f1' → K (compose f1' f2')
            | R f1' → R (compose f1' f2'))
  | R f2' → R (compose f1 f2')

?val rec[2] compose : Filter → Filter → Filter = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose f1' f2')
            | K f1' → K (compose f1' f2'))
  | R f2' → R (compose f1 f2')

(* A variant of the [Filter] type that is less lazy (only the K constuctor
   blocks computation). Mostly similar. *)

type SFilter2(α,β) = να X.{} → μβ Y.[R of Y | K of X]
type Filter2 = SFilter2(∞,∞)

type UFilter2 = {} → μY.[R of Y | K of Filter2]

check Filter2  ⊆ UFilter2
check UFilter2 ⊆ Filter2

val rec[1] filter2 : ∀A.UFilter2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

val rec[2] filter2 : ∀A.Filter2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

?val rec[1] filter2 : ∀A.Filter2 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f {} of
    | R f' → filter2 (fun _ → f') tl
    | K f' → fun _ → (hd, filter2 f' tl)

val rec[1] compose2 : UFilter2 → UFilter2 → Filter2 = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {})

val rec[3] compose2 : Filter2 → Filter2 → Filter2 = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {})

?val rec[2] compose2 : Filter2 → Filter2 → Filter2 = fun f1 f2 _ →
  case f2 {} of
  | K f2' → (case f1 {} of
            | R f1' → R (compose2 (fun _ → f1') f2' {})
            | K f1' → K (compose2 f1' f2'))
  | R f2' → R (compose2 f1 (fun _ → f2') {})

(* A third variant where the unit type is moved inside the variant type. This
   is again very similar, but [compose3] fails to type-check, although there
   is a workaround (see bellow for explanations). *)

type Filter3 = νX.μY.[R of Y | K of {} → X]

type UFilter3 = μY.[R of Y | K of {} → Filter3]

check Filter3  ⊆ UFilter3
check UFilter3 ⊆ Filter3

check Filter2      ⊆ {} → Filter3
check {} → Filter3 ⊆ Filter2

val rec[1] filter3 : ∀A.UFilter3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

val rec[2] filter3 : ∀A.Filter3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

?val rec[1] filter3 : ∀A.Filter3 → Stream(A) → Stream(A) =
  fun f s →
    let (hd, tl) = s {} in
    case f of
    | R f' → filter3 f' tl
    | K f' → fun _ → (hd, filter3 (f' {}) tl)

(* The following example fails, because in the typing of [R (compose3 ...)].
   This term is not normal, hence we cannot assume that the size of the stream
   is non-zero. *)
?val rec[1] compose3 : UFilter3 → UFilter3 → Filter3 = fun f1 f2 →
  case f2 of
  | K f2' → (case f1 of
             | R f1' → R (compose3 f1' (f2' {}))
             | K f1' → K (fun _ → compose3 (f1' {}) (f2' {})))
  | R f2' → R (compose3 f1 f2')

?val rec[2] compose3 : UFilter3 → UFilter3 → Filter3 = fun f1 f2 →
  case f2 of
  | K f2' → (case f1 of
             | R f1' → R (compose3 f1' (f2' {}))
             | K f1' → K (fun _ → compose3 (f1' {}) (f2' {})))
  | R f2' → R (compose3 f1 f2')

(* A workaround is still possible. *)
val compose3 : Filter3 → Filter3 → Filter3 = fun f1 f2 →
  compose2 (fun _ → f1) (fun _ → f2) {}

val rec[1] compose3' : UFilter3 → UFilter3 → Filter2 = fun f1 f2 _ →
  case f2 of
  | K f2' → (case f1 of
             | R f1' → R (compose3' f1' (f2' {}) {})
             | K f1' → K (compose3' (f1' {}) (f2' {})))
  | R f2' → R (compose3' f1 f2' {})

val compose3' : Filter3 → Filter3 → Filter3 = fun f1 f2 →
  compose3' f1 f2 {}

(* Bijection between nat stream and filters. *)

include "nat.typ"

val rec[1] filter_to_nat : UFilter → Stream(Nat) = fun s _ →
  case s {} of
  | R s → let (n, r) = filter_to_nat s {} in (S n, r)
  | K s → (0, filter_to_nat s)

(* Unfolding if not using [UFilter], but with size preservation. *)
val rec[3] filter_to_nat : ∀α.SFilter(α,∞) → SStream(α,Nat) = fun s _ →
  case s {} of
  | R s → let (n, r) = filter_to_nat s {} in (S n, r)
  | K s → (0, filter_to_nat s)

val rec[1] nat_to_filter : Stream(Nat) → Filter = fun s _ →
  let (n, s) = s {} in
  let rec fn = fun n _ →
    case n of
    | Z → K (nat_to_filter s)
    | S p → R (fn p)
  in
  fn n {}

(* Size-preserving version of the above (needs unrolling). *)
val rec[2] nat_to_filter : ∀α.SStream(α,Nat) → SFilter(α,∞) = fun s _ →
  let (n, s) = s {} in
  let rec fn : ∀α.SFilter(α,∞) → Nat → SFilter(α+1,∞) = fun s n →
    case n of
    | Z   → (fun _ → K s)
    | S p → (fun _ → R (fn s p))
  in
  fn (nat_to_filter s) n {}

(* The same using the less lazy streams of [Filter2]. *)

val rec[1] filter2_to_nat : UFilter2 → Stream(Nat) = fun s _ →
  case s {} of
  | R s → let (n, r) = filter2_to_nat (fun _ → s) {} in (S n, r)
  | K s → (0, filter2_to_nat s)

val rec[3] filter2_to_nat : ∀α.SFilter2(α,∞) → SStream(α,Nat) = fun s _ →
  case s {} of
  | R s → let (n, r) = filter2_to_nat (fun _ → s) {} in (S n, r)
  | K s → (0, filter2_to_nat s)

val rec[1] nat_to_filter2 : Stream(Nat) → Filter2 = fun s _ →
  let (n, s) = s {} in
  let rec fn = fun n →
    case n of
    | Z → K (nat_to_filter2 s)
    | S p → R (fn p)
  in fn n

val rec[2] nat_to_filter2 : ∀α.SStream(α,Nat) → SFilter2(α,∞) = fun s _ →
  let (n, s) = s {} in
  let rec fn : ∀α.SFilter2(α,∞) → Nat → SFilter2(α+1,∞) = fun s n _ →
    case n of
    | Z → K s
    | S p → R (fn s p {})
  in
  fn (nat_to_filter2 s) n {}
