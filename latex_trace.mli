open Ast
open Trace

type latex_output =
  | Kind of (bool * kind)
  | Term of (bool * term)
  | Text of string
  | List of latex_output list
  | SProof of sub_proof
  | TProof of typ_proof
  | Ordinals

val output : out_channel -> latex_output -> unit
val to_string : latex_output -> string
