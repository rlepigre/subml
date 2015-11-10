open Bindlib
open Util

(****************************************************************************
 *                         AST for kinds (or types)                         *
 ****************************************************************************)

(* Orientation for binder constraints. *)
type orient = GE | LE

(* Abstract syntax tree for types. *)
type kind =
  (**** Main type constructors ****)
  (* Type variable. *)
  | TVar of kind variable
  (* Function type: A ⇒ B. *)
  | Func of kind * kind
  (* Product (record) type: {l1 : A1 ; ... ; ln : An}. *)
  | Prod of (string * kind) list
  (* Bounded quantifiers: ∀/∃X [= A] </> A1,...,An B. *)
  | FAll of (kind, kind option * (orient * kind) option * kind) binder
  | Exis of (kind, kind option * (orient * kind) option * kind) binder
  (* Least and greatest fixpoint: μX A, νX A. *)
  | FixM of (kind, kind) binder
  | FixN of (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | TDef of type_def * kind array
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon) - used for subtyping. *)
  | TCst of type_constant
  (* Unification variables - used for typechecking. *)
  | UVar of uvar

(* Occurence markers for variables. *)
and occur =
  | Non   (* Do not occur. *)
  | Pos   (* Occurs positively only. *)
  | Neg   (* Occurs negatively only. *)
  | Both  (* Occurs both positively and negatively. *)
  | InEps (* Occurs under epsilon (special case). *)

(* Type definition (user defined type). *)
and type_def =
  (* Name of the type constructor. *)
  { tdef_name  : string
  (* Arity of the constructor. *)
  ; tdef_arity : int
  (* Definition of the constructor. *)
  ; tdef_value : (kind, kind) mbinder }

(* Epsilon constant.
 * In the constant
 *   { cst_key = i; cst_kind = bound; witness = t;  witness_kind = k }
 * the kind k sould be of one of the forms:
 *  - "Forall(bound, fun x -> k' x)",
 *  - "Exists(bound, fun x -> k' x)".
 * In the first case, the constant denotes a type Φ such that t is not of
 * type "k' Φ".
 * In the second case, the constant denotes a type Φ such that t is of
 * type "k' Φ".
 *)
and type_constant =
  (* An integer key for identifying the cst_cell in sets and maps. *)
  { cst_key      : int
  (* The bounds keeping track of the properties of the constant comming
     from its original quantifier. *)
  ; cst_kind     : (orient * (kind, kind list) binder) option
  (* The witness term and its kind. *)
  ; witness      : term
  ; witness_kind : kind }

(* Unification variable identified by a key and possibly a value. *)
and uvar =
  (* Unique key identifying the variable. *)
  { uvar_key         : int
  (* Value of the variable managed as in a union-find algorithm. *)
  ; mutable uvar_val : kind option }

(****************************************************************************
 *                     AST for expressions (or terms)                       *
 ****************************************************************************)

(* Abstract syntax tree for terms. *)
and term = term' position
and term' =
  (**** Main term constructors ****)
  (* Type coercion. *)
  | Coer of term * kind
  (* Free λ-variable. *)
  | LVar of term variable
  (* λ-abstraction. *)
  | LAbs of kind option * (term, term) binder
  (* Application. *)
  | Appl of term * term
  (* Record. *)
  | Reco of (string * term) list
  (* Projection. *)
  | Proj of term * string
  (* User-defined term. *)
  | VDef of value_def
  (* Print a string (side effect) and behave like the term. *)
  | Prnt of string * term
  (* Fixpoint combinator. *)
  | FixY
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(s,A,B) is a witness that there is a
     termed (nemed s) such that t has type A and does not have type B *)
  | Cnst of (string * kind * kind)
  
and value_def =
  (* Name of the value. *)
  { name  : string
  (* The corresponding term. *)
  ; value : term
  (* Raw version of the term (i.e. no anotations). *)
  ; ttype : kind option }

(****************************************************************************
 *                   Frequently used types and functions                    *
 ****************************************************************************)

(* Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

(* State. *)
type state =
  { tenv : typ_env
  ; venv : val_env }

let initial_state : unit -> state = fun () ->
  { tenv = Hashtbl.create 17
  ; venv = Hashtbl.create 17 }

(* Bindbox type shortcuts. *)
type tbox = term bindbox
type kbox = kind bindbox

(* Kind variable management. *)
let mk_free_tvar : kind variable -> kind =
  fun x -> TVar(x)

let new_tvar : string -> kind variable =
  new_var mk_free_tvar

(* Term variable management. *)
let mk_free_lvar : pos -> term variable -> term =
  fun p x -> in_pos p (LVar(x))

let new_lvar : pos -> string -> term variable =
  fun p -> new_var (mk_free_lvar p)

let new_lvar' : string -> term variable =
  new_lvar dummy_position

(****************************************************************************
 *                     Smart constructors for kinds                         *
 ****************************************************************************)

let tvar : string -> kbox =
  fun x -> box_of_var (new_tvar x)

let func : kbox -> kbox -> kbox =
  box_apply2 (fun t u -> Func(t,u))

let prod : (string * kbox) list -> kbox =
  fun fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> Prod(fs)) (box_list fs)

(* Auxiliary function for fall and exis. *)
let blift : (kbox option * (orient * kbox) option * kbox)
  -> (kind option * (orient * kind) option * kind) bindbox =
  fun (eq,bnd,t) ->
    let bnd =
      match bnd with
      | None       -> None
      | Some (o,k) -> Some (box_apply (fun k -> (o,k)) k)
    in
    box_triple (box_opt eq) (box_opt bnd) t

let fall : string
  -> (kbox -> (kbox option * (orient * kbox) option * kbox)) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x (fun k -> blift (f k)) in
    box_apply (fun b -> FAll(b)) b

let fall' : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    fall x (fun x -> (None, None, f x))

let exis : string
  -> (kbox -> (kbox option * (orient * kbox) option * kbox)) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x (fun k -> blift (f k)) in
    box_apply (fun b -> Exis(b)) b

let exis' : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    exis x (fun x -> (None, None, f x))

let tdef : type_def -> kbox array -> kbox =
  fun td ks -> box_apply2 (fun td ks -> TDef(td,ks)) (box td) (box_array ks)

let fixn : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x f in
    box_apply (fun b -> FixN(b)) b

let fixm : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x f in
    box_apply (fun b -> FixM(b)) b

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = incr c; UVar {uvar_key = !c; uvar_val = None} in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(****************************************************************************
 *                     Definition of widely used types                      *
 ****************************************************************************)

let fix_kind : kind =
  unbox (fall' "X" (fun x -> func (func (func x x) x) x))

let bot : kind =
  unbox (fall' "X" (fun x -> x))

let top : kind =
  unbox (exis' "X" (fun x -> x))

(****************************************************************************
 *              Functional constructors with position for terms             *
 ****************************************************************************)

let coer_p : pos -> term -> kind -> term =
  fun p t k -> in_pos p (Coer(t,k))

let lvar_p : pos -> term variable -> term =
  fun p x -> in_pos p (LVar(x))

let labs_p : pos -> kind option -> (term, term) binder -> term =
  fun p ko b -> in_pos p (LAbs(ko,b))

let appl_p : pos -> term -> term -> term =
  fun p t u -> in_pos p (Appl(t,u))

let reco_p : pos -> (string * term) list -> term =
  fun p fs -> in_pos p (Reco(fs))

let proj_p : pos -> term -> string -> term =
  fun p t l -> in_pos p (Proj(t,l))

let vdef_p : pos -> value_def -> term =
  fun p v -> in_pos p (VDef(v))

let prnt_p : pos -> string -> term -> term =
  fun p s t -> in_pos p (Prnt(s,t))

let fixy_p : pos -> term =
  fun p -> in_pos p FixY

let cnst_p : pos -> (string * kind * kind) -> term =
  fun p c -> in_pos p (Cnst(c))
 
(****************************************************************************
 *                     Smart constructors for terms                         *
 ****************************************************************************)

let coer : pos -> tbox -> kbox -> tbox =
  fun p -> box_apply2 (coer_p p)

let lvar : pos -> term variable -> tbox =
  fun p x -> box_of_var x

let labs : pos -> kbox option -> string position ->
           (tbox -> tbox) -> tbox =
  fun p ko x f ->
    box_apply2 (labs_p p) (box_opt ko) (bind (lvar_p x.pos) x.elt f)

let appl : pos -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (appl_p p)

let reco : pos -> (string * tbox) list -> tbox =
  fun p fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> reco_p p fs) (box_list fs)

let proj : pos -> tbox -> string -> tbox =
  fun p t l -> box_apply (fun t -> proj_p p t l) t

let vdef : pos -> value_def -> tbox =
  fun p vd -> box (vdef_p p vd)

let prnt : pos -> string -> tbox -> tbox =
  fun p s -> box_apply (prnt_p p s)

let fixy : pos -> tbox =
  fun p -> box (fixy_p p)

(* Build a constant. Useful during typing. *)
let cnst : string -> kind -> kind -> term =
  fun s a b -> dummy_pos (Cnst(s,a,b))
