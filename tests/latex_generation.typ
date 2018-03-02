(* Test and example of LaTeX generation. *)

include "list.typ"

(* Type definition (automatic folding). *)

type F(X) = [ Nil | Cons of X ]

set texfile "tests/latex_generation.tex"

latex {
  \documentclass{article}
  \setlength{\pdfpagewidth}{32000pt}
  \setlength{\paperwidth}{32000pt}
  \usepackage{unicode-math}
  \usepackage{bussproofs}
  \include{macros}
  \begin{document}
  \begin{center}
    \tiny
    ##flatten2#
  \end{center}
  \end{document}
}
