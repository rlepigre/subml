(** Size change principle. This module implements a decision procedure based
    on the work of Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL
    2001). It is used by PML to check that typing and subtyping proofs are
    well-founded. *)

(** Representation of the set with three elements: -1, 0 and ∞. *)
type cmp = Min1 | Zero | Infi

(** [cmp_to_string c] returns a string representation of the given [cmp]
    element on one character. *)
val cmp_to_string : cmp -> string

(** Size change matrix. *)
type matrix = { w : int ; h : int ; tab : cmp array array }

(** Abstract type used to refer to function symbols. *)
type index

(** [int_of_index i] returns an [int] corresponding to the index [i]. *)
val int_of_index : index -> int

(** Special index denoting the entry point. *)
val root : index

(** A call [{callee; caller; matrix; is_rec}] represents a call to the
    function symbol with key [callee] by the function symbole with the
    key [caller]. The [matrix] gives the relation between the parameters
    of the caller and the callee. The coefficient [matrix.(a).(b)] give
    the relation between the [a]-th parameter of the caller and the
    [b]-th argument of the callee. The boolean [is_rec] is true when the
    call is a reccursive call (i.e. a call to a generalised hypothesis
    lower in the tree. It is [false] for every call to subtyping in the
    typing algorithm and the same goes for rules introducing a new
    induction hypothesis. Every other call refers to a previously
    introduced induction hypothesis and its boolean is [true]. *)
type call =
  { callee : index  (** Key of the function symbol being called. *)
  ; caller : index  (** Key of the calling function symbol. *)
  ; matrix : matrix (** Size change matrix of the call. *)
  ; is_rec : bool   (** Indicates if this is a recursive call. *) }

(** The representation of the call graph. *)
type call_graph
type t = call_graph

(** [create ()] returns a new, empty call graph. *)
val create : unit -> t

(** [copy g] returns a copy of the call graph [g]. *)
val copy : t -> t

(** [is_empty g] indicates whether the call graph [g] contains calls. *)
val is_empty : t -> bool

(** [add_call g c] adds the call [c] to the call graph [g]. *)
val add_call : t -> call -> unit

(** [create_symbol g name args] creates a new function symbol with the name
    [name] and using [args] as the name of its arguments. Note that the new
    symbol will have the arity [Array.length args]. The value returned is
    the [index], which can be used in a [call]. *)
val create_symbol : t -> string -> string array -> index

(** [arity i g] returns the arity of the symbol with index [i] in the call
    graph [g]. *)
val arity : index -> t -> int

(** Flag controling inlining. The default value is [true]. *)
val do_inline : bool ref

(** [inline g] inlines the call graph [g], which is useful for printing more
    consise call graphs, or to store smaller call graphs. Note that if the
    flag [do_inline] is set of [false], this function returns an unchanged
    call graph. *)
val inline : t -> t

(** [sct g] runs the decision procedure on the call graph [g]. *)
val sct : t -> bool

(** [latex_print_calls ff g] prints the call graph [g] using a LaTeX format
    on the [Format.formatter] [ff]. *)
val latex_print_calls : Format.formatter -> t -> unit
