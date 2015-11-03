open Bindlib
open Util

(****************************************************************************
 *                         AST for kinds (or types)                         *
 ****************************************************************************)

(* Abstract syntax tree for types. *)
type kind =
  (**** Main type constructors ****)
  (* Type variable. *)
  | TVar of kind variable
  (* Function type: A ⇒ B. *)
  | Func of kind * kind
  (* Extensible product type with default field: { A ; l : B }. *)
  | Prod of kind * string * kind
  (* Unit type (nullary product): {}. *)
  | Unit
  (* Quantifiers (with bounds): ∀/∃X X</>A1,...,An B. *)
  | FAll of bounds option * (kind, kind) binder
  | Exis of bounds option * (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | TDef of type_def * kind array
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon) - used for subtyping. *)
  | TCst of type_constant
  (* Unification variables - used for typechecking. *)
  | UVar of uvar

(* Bounds for quantifiers. *)
and orient = GE | LE
and bounds = orient * (kind, kind) binder list

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
  ; tdef_value : (kind, kind) mbinder
  (* Precomputed variance. *)
  ; tdef_occur : occur array }

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
  ; cst_kind     : bounds option
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
  (* Type abstraction. *)
  | TAbs of (kind, term) binder
  (* Free λ-variable. *)
  | LVar of term variable
  (* λ-abstraction. *)
  | LAbs of kind option * (term, term) binder
  (* Application. *)
  | Appl of term * term
  (* Local let definition. *)
  | LLet of bool * pos array * (term, term array) mbinder
  (* Extensible record with only one field. *)
  | Reco of term * string * term
  (* Unit element. *)
  | URec
  (* Projection. *)
  | Proj of term * string
  (* User-defined term. *)
  | VDef of value_def
  (* Print a string (side effect) and behave like the term. *)
  | Prnt of string * term
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(s,A,B) is a witness that there is a
     termed (nemed s) such that t has type A and does not have type B *)
  | Cnst of (string * kind * kind)
  
and value_def =
  (* Name of the value. *)
  { name           : string
  (* The corresponding term. *)
  ; mutable value  : term
  (* Raw version of the term (i.e. no anotations). *)
  ; mutable ttype  : kind option
  (* Flag for tracing variable. *)
  ; mutable trace  : bool }

(****************************************************************************
 *                   Frequently used types and functions                    *
 ****************************************************************************)

(* Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

(* Bindbox type shortcuts. *)
type termbox = term bindbox
type kindbox = kind bindbox

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

let tvar : string -> kindbox =
  fun x -> box_of_var (new_tvar x)

let func : kindbox -> kindbox -> kindbox =
  box_apply2 (fun t u -> Func(t,u))

let prod : kindbox -> string * kindbox -> kindbox =
  fun dk (l,k) -> box_apply2 (fun dk k -> Prod(dk,l,k)) dk k

let uNit : kindbox =
  box Unit

let fall : bounds bindbox option -> string -> (kindbox -> kindbox)
           -> kindbox =
  fun bo x f ->
    let b = bind mk_free_tvar x f in
    box_apply2 (fun bo b -> FAll(bo,b)) (box_opt bo) b

let exis : bounds bindbox option -> string -> (kindbox -> kindbox)
           -> kindbox =
  fun bo x f ->
    let b = bind mk_free_tvar x f in
    box_apply2 (fun bo b -> FAll(bo,b)) (box_opt bo) b


(* TDef of type_def * kind array *) (* TODO *)
(* TCst of type_constant *) (* TODO *)

(*
let tdef td a = box_apply2 (fun td a -> TDef(td,a)) td (box_array a)
let tuvar v = box (TUVar v)
*)

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = UVar {uvar_key = !c; uvar_val = None} in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(****************************************************************************
 *              Functional constructors with position for terms             *
 ****************************************************************************)

let coer_p : pos -> term -> kind -> term =
  fun p t k -> in_pos p (Coer(t,k))

let tabs_p : pos -> (kind, term) binder -> term =
  fun p b -> in_pos p (TAbs(b))

let lvar_p : pos -> term variable -> term =
  fun p x -> in_pos p (LVar(x))

let labs_p : pos -> kind option -> (term, term) binder -> term =
  fun p ko b -> in_pos p (LAbs(ko,b))

let appl_p : pos -> term -> term -> term =
  fun p t u -> in_pos p (Appl(t,u))

let llet_p : pos -> bool -> pos array -> (term, term array) mbinder -> term =
  fun p r ps b -> in_pos p (LLet(r,ps,b))

let reco_p : pos -> term -> string * term -> term =
  fun p td (l,t) -> in_pos p (Reco(td,l,t))

let urec_p : pos -> term =
  fun p -> in_pos p URec

let proj_p : pos -> term -> string -> term =
  fun p t l -> in_pos p (Proj(t,l))

let vdef_p : pos -> value_def -> term =
  fun p v -> in_pos p (VDef(v))

let prnt_p : pos -> string -> term -> term =
  fun p s t -> in_pos p (Prnt(s,t))

let cnst_p : pos -> (string * kind * kind) -> term =
  fun p c -> in_pos p (Cnst(c))
 
(****************************************************************************
 *                     Smart constructors for terms                         *
 ****************************************************************************)

let coer : pos -> termbox -> kindbox -> termbox =
  fun p -> box_apply2 (coer_p p)

let tabs : pos -> string -> (kindbox -> termbox) -> termbox =
  fun p x f -> box_apply (tabs_p p) (bind (fun x -> TVar(x)) x f)

let lvar : pos -> string -> termbox =
  fun p x -> box_of_var (new_lvar p x)

let labs : pos -> kindbox option -> string position ->
           (termbox -> termbox) -> termbox =
  fun p ko x f ->
    box_apply2 (labs_p p) (box_opt ko) (bind (lvar_p x.pos) x.elt f)

let appl : pos -> termbox -> termbox -> termbox =
  fun p -> box_apply2 (appl_p p)

let llet : pos -> bool -> string array -> pos array
           -> (term bindbox array -> term array bindbox) -> term bindbox =
  fun p r ns ps f -> box_apply (llet_p p r ps) (mbind (lvar_p p) ns f)

let reco : pos -> termbox -> string * termbox -> termbox =
  fun p dt (l,t) -> box_apply2 (fun dt t -> reco_p p dt (l,t)) dt t

let urec : pos -> termbox =
  fun p -> box (urec_p p)

let proj : pos -> termbox -> string -> termbox =
  fun p t l -> box_apply (fun t -> proj_p p t l) t

(* VDef of value_def *) (* TODO *)

let prnt : pos -> string -> termbox -> termbox =
  fun p s -> box_apply (prnt_p p s)

(* Build a constant. Useful during typing. *)
let cnst : string -> kind -> kind -> term =
  fun s a b -> dummy_pos (Cnst(s,a,b))
