open Format
open Ast
open Util

(* code shared with other printing *)

(* usefull function *)
val print_list : (formatter -> 'a -> unit) -> string -> formatter -> 'a list -> unit
val print_array : (formatter -> 'a -> unit) -> string -> formatter -> 'a array -> unit
val is_tuple : (string * 'a) list -> bool

(* function related to simplification of
   unused induction rule and the resulting simplification of ordinals *)
val ignored_ordinals : ordinal list ref
val onorm : ordinal -> ordinal

(* when true, print_ordinal as variables (as if they were no witnesses *)
val simplified_ordinals : bool ref

(* function to search, print and reset tables of ordinals and epsilon,
   this allow to print a simple name, and latex the long definition.
   without this, printing is unreadable *)
val reset_epsilon_tbls : unit -> unit
val search_type_tbl : term -> (kind, kind) Bindlib.binder -> bool -> string * int
val search_term_tbl : (term, term) Bindlib.binder -> kind -> kind -> string * int
val search_ordinal_tbl : ordinal -> int
val print_epsilon_tbls : formatter -> unit
(* pointer are exported for the latex versiob of the print function *)
val ordinal_tbl : (ordinal * int) list ref
val epsilon_term_tbl : ((term, term) Bindlib.binder * (string * int * kind * kind)) list ref
val epsilon_type_tbl : ((kind, kind) Bindlib.binder * (string * int * term * bool)) list ref

(* unicode printing *)

(* Pretty-printer for terms. If the boolean is true, definitions are unfolded,
otherwise the name of the defined type is used instead. *)
val print_term : bool -> formatter -> term -> unit

(* Pretty-printer for kind. If the boolean is true, definitions are unfolded,
otherwise the name of the defined type is used instead. *)
val print_kind : bool -> formatter -> kind -> unit

(* Pretty-printer for a kind definition. If the boolean is true, definitions
are unfolded, otherwise the name of the defined type is used instead. *)
val print_kind_def : bool -> formatter -> type_def -> unit

(* Pretty-printer for an ordinal *)
val print_ordinal : bool -> formatter -> ordinal -> unit

(* various *)
val print_term_in_subtyping : bool ref
val find_tdef : kind -> type_def
val print_position : formatter -> Location.t -> unit

type output = { mutable f : 'a. ('a, formatter, unit) format -> 'a }
val output : output
