open Ast

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * type_def
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * Sct.calls_graph
  | TProof  of typ_prf
  | Sct     of Sct.calls_graph
  | Witnesses

val to_string : latex_output -> string

val output : out_channel -> latex_output -> unit
