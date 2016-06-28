open Ast

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * type_def
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * ((int * int) list * Sct.calls)
  | TProof  of typ_prf
  | Sct     of ((int * int) list * Sct.calls) list
  | Witnesses

val to_string : latex_output -> string

(*
val output : out_channel -> latex_output -> unit
*)
