type F(A,X) = [ Nil | Cons of { hd : A; tl : X } ]
type List(A) = μX F(A,X)
type G(A,B) = [ Cons of { hd : A; tl : B } ]


val rec split : ∀A G(A,List(A)) → List(A) × List(A) =
  fun l ↦
    case l of
    | x::l → case l of
             | []   → (x::[], [])
             | y::l → let (l1,l2) = split (y::l) in (x::l2, l1)

val rec split2 : ∀o ∀A (μo X F(A,X)) → (μo X F(A,X)) × (μo X F(A,X)) =
  fun l →
    case l of
    | []   → ([], [])
    | x::l → let (l1,l2) = split2 l in (x::l2, l1)

val rec merge : ∀A (A → A → Bool) → List(A) → List(A) → List(A) =
  fun cmp l1 l2 →
    case l1 of
    | []      → l2
    | x1::l1' → (case l2 of
                | []      → l1
                | x2::l2' → if cmp x1 x2 then
                                 x1 :: merge cmp l1' l2
                            else x2 :: merge cmp l1 l2')

val rec sort : ∀A (A → A → Bool) → List(A) → List(A) =
  fun cmp l →
    case l of
    | []   → []
    | x::l → (case l of
              | []       → l
              | y::l → let (m1, m2) = split2 l in
                       let l1 = sort cmp (x::m1) in
                       let l2 = sort cmp (y::m2) in
                       merge cmp l1 l2)


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
