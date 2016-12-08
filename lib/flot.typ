type S(A) = νX {} → A * X
type F = νX μY [ R of Y | K of {} → X ]
type SF1(α) = ναX μY [ R of Y | K of {} → X ]
type SF2(α) = νX μαY [ R of Y | K of {} → X ]


val rec 2 filter : ∀A F → S(A) → S(A) = fun f s →
  let (hd, tl) = s {} in
  case f of
  | R f' → filter f' tl
  | K f' → fun _ → (hd, filter (f' {}) tl)

(* FIXME *)
?val rec compose : F → F → F = fun f1 f2 →
  (case f2 of
  | K f2' → (case f1 of
            | R f1' → R (compose f1' (f2' {}))
            | K f1' → K (fun _ → compose (f1' {}) (f2' {})))
  | R f2' → R (compose f1 f2'))
