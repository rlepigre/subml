open Ast
open Proof_trace

type latex_output =
  | Kind of int * bool * kind
  | KindDef of int * type_def
  | Term of int * bool * term
  | Text of string
  | List of latex_output list
  | SProof of sub_proof
  | TProof of typ_proof
  | Witnesses

val output : out_channel -> latex_output -> unit
val to_string : latex_output -> string
