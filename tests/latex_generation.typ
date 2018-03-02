(* Test and example of LaTeX generation. *)

include "list.typ"

(* Type definition (automatic folding). *)

type F(X) = [ Nil | Cons of X ]

set texfile "tests/latex_generation.tex"

latex {
  \documentclass{article}
  \setlength{\pdfpagewidth}{10000pt}
  \setlength{\paperwidth}{10000pt}
  \usepackage{amssymb,amsmath,amsthm} %must be before unicode-math
  \usepackage[mathletters]{ucs}
  \usepackage[utf8x]{inputenc}
  \usepackage{bussproofs}
  \include{macros}
  \begin{document}
  \begin{center}
    \tiny
    ##flatten2#
  \end{center}
  \end{document}
}
