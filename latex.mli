open Format
open Ast

(* Pretty-printer for terms. If the boolean is true, definitions are unfolded,
otherwise the name of the defined type is used instead. *)
val print_term : bool -> out_channel -> term -> unit

(* Pretty-printer for kind. If the boolean is true, definitions are unfolded,
otherwise the name of the defined type is used instead. *)
val print_kind : bool -> out_channel -> kind -> unit

(* Pretty-printer for a kind definition. If the boolean is true, definitions
are unfolded, otherwise the name of the defined type is used instead. *)
val print_kind_def : bool -> out_channel -> type_def -> unit

val print_ordinal : out_channel -> ordinal -> unit
