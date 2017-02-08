(*****************************************************************************)
(**{3                 Size change termination principle                     }*)
(**         Chin Soon Lee, Neil D. Jones, Amir M. Ben-AmramPOPL2001          *)
(*****************************************************************************)

open Format

type cmp =
  | Less (** argument is stricly smaller than the calling parameter *)
  | Leq  (** argument is less of equal than the calling parameter   *)
  | Unknown (** no relation is known between the argument and the parameter *)

(**a call g(x0-1,x1,x1-1) inside f(x0,x1) is
   represented by (g_n, f_n, [|[| Less; Unknown; Unknown |];
                               [| Unknown; Leq; Less  |]|], b)

   more precisely, a call (i,j,m) represents a call
   to the function numbered i inside the function numbered j.
   m is a matrix. the coefficient m.(a).(b) give the relation
   between the a-th parameter of the caller and the b-th argument
   of the called function.

   The boolean in call indicates a recursive call, that must not be
   removed by inlining. The boolean is true when the call is a recursive
    call. i.e. A call to a generalised hypothesis lower in the tree.
    More precisely, each subtyping in a typing, each rule introducing
    a new induction hypothesis has a false boolean. All other call
    are call to an induction hypothesis and have a true boolean.
*)
type index
type call = index * index * cmp array array * bool

val call_index : call -> index

(** A list of calls to be constructed then checked *)
type call_table
type t = call_table

val init_table : unit -> call_table
val copy : call_table -> call_table

val root : index

(** Creation of a new function, return the function index in the table *)
val new_function : call_table -> string -> string list -> index

(** Creation of a new call *)
val new_call : call_table -> call -> unit

(** Gives the arity of a given function *)
val arity : index-> call_table -> int

val prInd : Format.formatter -> index -> unit
val prCmp : Format.formatter -> cmp   -> unit
val latex_print_calls : formatter -> call_table -> unit

val strInd : index -> string
val strCmp : cmp   -> string

(** Returns true for a table with no call *)
val is_empty : call_table -> bool

(** True (by default) to activate inlining *)
val do_inline : bool ref

(** Run the sct decision procedure *)
val sct : call_table -> bool

(** Run the inlining only. Useful to print or store a smaller call_graph.
    [inline] does nothing if [!do_inline] is false *)
val inline : call_table -> call_table
