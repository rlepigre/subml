open Ast

type print_mode = Ascii | Latex

let print_mode = ref Ascii

let print_kind u ch = match !print_mode with
  | Ascii -> Print.print_kind u ch
  | Latex -> Latex.print_kind u ch

let print_kind_def u ch = match !print_mode with
  | Ascii -> Print.print_kind_def u ch
  | Latex -> Latex.print_kind_def u ch

let print_term u ch = match !print_mode with
  | Ascii -> Print.print_term u ch
  | Latex -> Latex.print_term u ch

let print_ordinal ch =
  match !print_mode with
  | Ascii -> Print.print_ordinal ch
  | Latex -> Latex.print_ordinal ch

let reset_ordinals = Print.reset_ordinals
