open Format
open Ast

val print_list : (formatter -> 'a -> unit) -> string -> formatter -> 'a list -> unit

val print_array : (formatter -> 'a -> unit) -> string -> formatter -> 'a array -> unit

val ignored_ordinals : ordinal list ref

(* Pretty-printer for terms. *)
val print_term : out_channel -> term -> unit

(* Pretty-printer for kind. If the boolean is true, definitions are unfolded,
otherwise the name of the defined type is used instead. *)
val print_kind : bool -> out_channel -> kind -> unit

(* Pretty-printer for a kind definition. If the boolean is true, definitions
are unfolded, otherwise the name of the defined type is used instead. *)
val print_kind_def : bool -> out_channel -> type_def -> unit
