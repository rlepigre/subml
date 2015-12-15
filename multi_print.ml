open Ast

type print_mode = Ascii | Latex

let print_mode = ref Ascii

let print_kind ch = match !print_mode with
  | Ascii -> Print.print_kind ch
  | Latex -> Latex.print_kind ch

let print_kind_def ch = match !print_mode with
  | Ascii -> Print.print_kind_def ch
  | Latex -> Latex.print_kind_def ch

let print_term ch = match !print_mode with
  | Ascii -> Print.print_term ch
  | Latex -> Latex.print_term ch
