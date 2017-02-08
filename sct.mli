(*****************************************************************************)
(**{3                 Size change termination principle                     }*)
(**         Chin Soon Lee, Neil D. Jones, Amir M. Ben-AmramPOPL2001          *)
(*****************************************************************************)

open Format

type cmp =
  | Min1 (** argument is stricly smaller than the calling parameter *)
  | Zero (** argument is less of equal than the calling parameter   *)
  | Infi (** no relation is known between the argument and the parameter *)

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
type matrix = { w : int ; h : int ; tab : cmp array array }
type call =
  { callee : index
  ; caller : index
  ; matrix : matrix
  ; is_rec : bool }

(** A list of calls to be constructed then checked *)
type call_graph
type t = call_graph

val create : unit -> t
val copy : t -> t

val root : index

(** Creation of a new function, return the function index in the table *)
val create_symbol : t -> string -> string array -> index

(** Creation of a new call *)
val add_call : t -> call -> unit

(** Gives the arity of a given function *)
val arity : index-> t -> int

val prInd : Format.formatter -> index -> unit
val prCmp : Format.formatter -> cmp   -> unit
val latex_print_calls : formatter -> t -> unit

val strInd : index -> string

(** Returns true for a table with no call *)
val is_empty : t -> bool

(** True (by default) to activate inlining *)
val do_inline : bool ref

(** Run the sct decision procedure *)
val sct : t -> bool

(** Run the inlining only. Useful to print or store a smaller t.
    [inline] does nothing if [!do_inline] is false *)
val inline : t -> t
