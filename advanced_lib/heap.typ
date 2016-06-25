type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]

type List(A) = μX F(A,X)

type G(A,B) = [ Cons of { hd : A; tl : B } ]

val rec split : ∀A G(A,List(A)) → List(A) × List(A) =
  fun l → case l of
  | Cons c →
    let x = c.hd in
    let l' = c.tl in
    case l' of
    | [] → (x::[], [])
    | Cons c' →
      let c = split (Cons c') in
      (x::c.2, c.1)

val rec split2 : ∀o ∀A (μo X F(A,X)) → (μo X F(A,X)) × (μo X F(A,X)) =
  fun l → case l of
  | [] → ([], [])
  | Cons c →
    let x = c.hd in
    let l' = c.tl in
    let q = split2 l' in
    (x::q.2, q.1)

val rec merge : ∀A (A → A → Bool) → List(A) → List(A) → List(A)
  = fun cmp l1 l2 → case l1 of
  | []      → l2
  | Cons c1 →
    (case l2 of
    | []      → l1
    | Cons c2 →
      if cmp c1.hd c2.hd then c1.hd :: merge cmp c1.tl l2
                         else c2.hd :: merge cmp l1    c2.tl)

val rec sort : ∀A (A → A → Bool) → List(A) → List(A)
  = fun cmp l → case l of
  | [] → []
  | Cons c1 →
    case c1.tl of
    | [] -> l
    | Cons c2 →
      let c = split2 c2.tl in
      let l1 = sort cmp (c1.hd::c.1) in
      let l2 = sort cmp (c2.hd::c.2) in
      merge cmp l1 l2

(*
latex {
\documentclass{article}

\setlength{\pdfpagewidth}{2000mm}
\setlength{\paperwidth}{2000mm}

\usepackage{bussproofs}
\include{macros}
\begin{document}
\begin{center}
\tiny
\begin{prooftree}
##split2#
\end{prooftree}
\end{center}
\end{document}
}
*)