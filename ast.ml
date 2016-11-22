(** Basic definition of the Ast of types and programs *)

open Bindlib
open Refinter
open Format
open Position

let map_opt : ('a -> 'b) -> 'a option -> 'b option = fun f o ->
  match o with None -> None | Some e -> Some (f e)

let iter_opt : ('a -> unit) -> 'a option -> unit = fun f o ->
  match o with None -> () | Some e -> f e

let from_opt : 'a option -> 'a -> 'a = fun o d ->
  match o with None -> d | Some e -> e

let from_opt' : 'a option -> (unit -> 'a) -> 'a = fun o f ->
  match o with None -> f () | Some e -> e

let map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list = fun f l ->
  List.map (fun (k, v) -> (k, f v)) l

(** {2         AST for kinds (or types), ordinals and terms              }  *)
(** Occurence markers for variables. *)
type occur =
  (** The variable does not occur. *)
  | Non
  (** The variable occurs only positively. *)
  | Pos
  (** The variable occurs only negatively. *)
  | Neg
  (** The variable occurs both positively and negatively. *)
  | All
  (** The variable occurs under an epsilon witness (special case). *)
  | Eps
  (** Special constructor for constructing the variance of definitions. *)
  | Reg of int * occur array

(** Ast of kinds (or types). *)
type kind =
  (** Main type constructors *)
  | KVari of kind variable
  (** Type variable. *)
  | KFunc of kind * kind
  (** Function type: A ⇒ B. *)
  | KProd of (string * kind) list
  (** Product (record) type: {l1 : A1 ; ... ; ln : An}. *)
  | KDSum of (string * kind) list
  (** Sum (variant) type: [C1 of A1 | ... | Cn of An]. *)
  | KKAll of (kind, kind) binder
  | KKExi of (kind, kind) binder
  (** Quantifiers over a type: ∀/∃X A. *)
  | KOAll of (ordinal, kind) binder
  | KOExi of (ordinal, kind) binder
  (** Quantifiers over an ordinal: ∀/∃o A. *)
  | KFixM of ordinal * (kind, kind) binder
  | KFixN of ordinal * (kind, kind) binder
  (** Least and greatest fixpoint: μα X A, να X A. *)
  | KDefi of type_def * ordinal array * kind array
  (** User-defined type applied to arguments: T(A1,...,An). *)
  | KDPrj of term * string
  (** Dot projection t.X. *)
  | KWith of kind * (string * kind)
  (** With clause A with X = B. *)
  (* Special constructors (not accessible to user) *)
  | KUCst of term * (kind, kind) binder
  | KECst of term * (kind, kind) binder
  (** Constants (a.k.a. epsilon) - used for subtyping. *)
  | KUVar of kuvar
  (** Unification variables - used for typechecking. *)
  | KTInt of int
  (** Integer tag for comparing kinds. *)
  | KMRec of ordinal refinter * kind
  | KNRec of ordinal refinter * kind
  (** Ordinal conjunction and disjunction *)

(** Type definition (user defined type). *)
and type_def =
  (* Name of the type constructor. *)
  { tdef_name     : string
  ; tdef_tex_name : string
  (* Arity of the constructor. *)
  ; tdef_oarity   : int
  ; tdef_karity   : int
  ; tdef_ovariance : occur array
  ; tdef_kvariance : occur array
  (* Definition of the constructor. *)
  ; tdef_value    : (ordinal, (kind, kind) mbinder) mbinder }

(** Unification variable identified by a key and possibly a value. *)
and kuvar =
  (* Unique key identifying the variable. *)
  { kuvar_key : int
  (* Value of the variable managed as in a union-find algorithm. *)
  ; kuvar_val : kind option ref
  ; kuvar_state : kuvar_state ref }

and kuvar_state = Free
  | Sum  of (string * kind) list
  | Prod of (string * kind) list

(** Abstract syntax tree for ordinals. *)
and ordinal =
  | OConv
  (** Ordinal large enough to ensure convergence of all fixpoints. *)
  | OSucc of ordinal
  (** Succesor *)
  | OLess of ordinal * ord_wit
  (** Ordinal created by the μl and νr rules *)
  | OUVar of ouvar * ordinal option
  (** Unification variables for ordinals. *)
  | OVari of ordinal variable
  (** Ordinal variable. *)
  | OTInt of int
  (** Integer tag used in decompose / recompose. *)

(** ordinal constraints to build above [OLess] witness *)
and ord_wit =
  | In     of term * (ordinal, kind) binder
  | NotIn  of term * (ordinal, kind) binder
  | WUVar of wuvar

and ouvar = ordinal option ref

and wuvar = ord_wit option ref

(** Abstract syntax tree for terms. *)
and term = term' position
and term' =
  (**** Main term constructors ****)
  (* Type coercion. *)
  | TCoer of term * kind
  (* Free λ-variable. *)
  | TVari of term' variable
  (* λ-abstraction. *)
  | TAbst of kind option * (term', term) binder
  (* Application. *)
  | TAppl of term * term
  (* Record. *)
  | TReco of (string * term) list
  (* Projection. *)
  | TProj of term * string
  (* Variant. *)
  | TCons of string * term
  (* Case analysis. *)
  | TCase of term * (string * term) list * term option
  (* User-defined term. *)
  | TDefi of value_def
  (* Print a string (side effect) and behave like the term. *)
  | TPrnt of string
  (* Fixpoint combinator. *)
  | TFixY of bool * int * (term', term) binder
  (* Lambda on a type, semantics via epsilon *)
  | TKAbs of (kind, term) binder
  (* Lambda on an ordinal, semantics via epsilon *)
  | TOAbs of (ordinal, term) binder
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | TCnst of ((term', term) binder * kind * kind)
  (* Integer tag. *)
  | TTInt of int

(** Term definition (user defined term) *)
and value_def =
  { name       : string      (* Name of the term. *)
  ; tex_name   : string      (* Latex name of the term. *)
  ; value      : term        (* Evaluated term. *)
  ; orig_value : term        (* Original term (not evaluated). *)
  ; ttype      : kind        (* Type of the term. *)
  ; proof      : typ_prf     (* Typing proof. *)
  ; calls_graph: Sct.calls_graph } (* SCT instance. *)

and typ_jdg = term * kind
and sub_jdg = term * kind * kind

and sub_rule =
  | Sub_Delay  of sub_prf ref
  | Sub_Lower
  | Sub_Func   of sub_prf * sub_prf
  | Sub_Prod   of sub_prf list
  | Sub_DSum   of sub_prf list
  | Sub_DPrj_l of typ_prf * sub_prf
  | Sub_DPrj_r of typ_prf * sub_prf
  | Sub_With_l of sub_prf
  | Sub_With_r of sub_prf
  | Sub_KAll_r of sub_prf
  | Sub_KAll_l of sub_prf
  | Sub_KExi_l of sub_prf
  | Sub_KExi_r of sub_prf
  | Sub_OAll_r of sub_prf
  | Sub_OAll_l of sub_prf
  | Sub_OExi_l of sub_prf
  | Sub_OExi_r of sub_prf
  | Sub_FixM_r of sub_prf
  | Sub_FixN_l of sub_prf
  | Sub_FixM_l of sub_prf
  | Sub_FixN_r of sub_prf
  | Sub_And_l  of sub_prf
  | Sub_And_r  of sub_prf
  | Sub_Or_l   of sub_prf
  | Sub_Or_r   of sub_prf
  | Sub_Ind    of int
  | Sub_Error  of string
and sub_prf =
  (* the integer is referenced by induction hyp *)
  term * kind * kind * int option * sub_rule

and typ_rule =
  | Typ_Coer   of sub_prf * typ_prf
  | Typ_KAbs   of typ_prf
  | Typ_OAbs   of typ_prf
  | Typ_Defi   of sub_prf
  | Typ_Prnt   of sub_prf
  | Typ_Cnst   of sub_prf
  | Typ_Func_i of sub_prf * typ_prf
  | Typ_Func_e of typ_prf * typ_prf
  | Typ_Prod_i of sub_prf * typ_prf list
  | Typ_Prod_e of typ_prf
  | Typ_DSum_i of sub_prf * typ_prf
  | Typ_DSum_e of typ_prf * typ_prf list * typ_prf option
  | Typ_TFix   of int * typ_prf ref
  | Typ_YH     of int * sub_prf
  | Typ_Hole   (* used by dummy_proof below *)
  | Typ_Error  of string
and typ_prf =
  term * kind * typ_rule

(** used by Typ_Link as initial value *)
let dummy_proof = (dummy_pos (TReco []), KProd [], Typ_Hole)

(** Unfolding unification variable indirections. *)
let rec repr : kind -> kind = function
  | KUVar({kuvar_val = {contents = Some k}}) -> repr k
  | k                                        -> k

(** Unfolding unification variable indirections and definitions *)
let rec full_repr : kind -> kind = function
  | KUVar({kuvar_val = {contents = Some k}}) -> full_repr k
  | KDefi({tdef_value = v}, os, ks) -> full_repr (msubst (msubst v os) ks)
  | KMRec(p,k) when Refinter.is_empty p -> full_repr k
  | KNRec(p,k) when Refinter.is_empty p -> full_repr k
  | k                               -> k

let rec orepr = function
  | OUVar({contents = Some o}, _) -> orepr o
  | OSucc o -> OSucc (orepr o)
  | o -> o

let rec wrepr = function
  | WUVar({contents = Some w}) -> wrepr w
  | w -> w

(** Printing function from "print.ml" *)
let fprint_term : (bool -> formatter -> term -> unit) ref =
  ref (fun _ -> assert false)

let fprint_kind : (bool -> formatter -> kind -> unit) ref =
  ref (fun _ -> assert false)

let fprint_ordinal : (bool -> formatter -> ordinal -> unit) ref =
  ref (fun _ -> assert false)

let ftry_fold_def : (kind -> kind) ref =
  ref (fun _ -> assert false)

(****************************************************************************
 *                   Frequently used types and functions                    *
 ****************************************************************************)

(** Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

let typ_env : typ_env = Hashtbl.create 17
let val_env : val_env = Hashtbl.create 17
let verbose : bool ref = ref false

(** Bindbox type shortcuts. *)
type tvar = term' variable
type tbox = term bindbox

type kvar = kind variable
type kbox = kind bindbox

type ovar = ordinal variable
type obox = ordinal bindbox

(** Kind variable management. *)
let mk_free_kvari : kind variable -> kind =
  fun x -> KVari(x)

let new_kvari : string -> kind variable =
  new_var mk_free_kvari

(** Term variable management. *)
let mk_free_tvari : term' variable -> term' =
  fun x -> TVari(x)

let new_tvari : string -> term' variable =
  new_var mk_free_tvari

(** Ordinal variable management. *)
let mk_free_ovari : ovar -> ordinal =
  fun o -> OVari(o)

let new_ovari : string -> ovar =
  new_var mk_free_ovari

(** sugaring for ordinals *)
let oconv = box OConv

let osucc o = box_apply (fun o -> OSucc o) o
let rec oadd o n = if n <= 0 then o else oadd (OSucc o) (n-1)

let oless_In    = box_apply3 (fun o t k -> OLess(o, In(t,k)))
let oless_NotIn = box_apply3 (fun o t k -> OLess(o,NotIn(t,k)))

(****************************************************************************
 *                     Smart constructors for kinds                         *
 ****************************************************************************)

let kvari : string -> kbox =
  fun x -> box_of_var (new_kvari x)

let kfunc : kbox -> kbox -> kbox =
  box_apply2 (fun t u -> KFunc(t,u))

let kprod : (string * kbox) list -> kbox =
  fun fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> KProd(fs)) (box_list fs)

let kdsum : (string * kbox) list -> kbox =
  fun cs ->
    let cs = List.map (fun (c,t) -> box_pair (box c) t) cs in
    box_apply (fun cs -> KDSum(cs)) (box_list cs)

let kkall : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KKAll(b)) (vbind mk_free_kvari x f)

let kkexi : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KKExi(b)) (vbind mk_free_kvari x f)

let koall : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KOAll(b)) (vbind mk_free_ovari x f)

let koexi : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KOExi(b)) (vbind mk_free_ovari x f)

let kdprj : tbox -> string -> kbox =
  fun t s ->
    box_apply (fun t -> KDPrj(t,s)) t

let kwith : kbox -> string -> kbox -> kbox =
  fun a s b ->
    box_apply2 (fun a b -> KWith(a,(s,b))) a b

let kdefi : type_def -> obox array -> kbox array -> kbox =
  fun td os ks ->
    let fn td os ks = KDefi(td,os,ks) in
    box_apply3 fn (box td) (box_array os) (box_array ks)

let kfixn0 : obox -> (kind, kind) binder -> kbox =
  fun o f ->
    box_apply (fun o -> KFixN(o,f)) o

let kfixn : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixN(o,b)) o b

let kfixm0 : obox -> (kind, kind) binder -> kbox =
  fun o f ->
    box_apply (fun o -> KFixM(o,f)) o

let kfixm : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixM(o,b)) o b

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar ?(state=Free) () = KUVar {
    kuvar_key = (incr c; !c);
    kuvar_val = ref None;
    kuvar_state = ref state;
  } in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(* Resset all counters. *)
let reset_all () =
  (* FIXME: should have everything in the ctxt *)
  reset_uvar ()

(****************************************************************************
 *                     Definition of widely used types                      *
 ****************************************************************************)

let bot : kind =
  unbox (kkall "X" (fun x -> box_of_var x))

let top : kind =
  unbox (kkexi "X" (fun x -> box_of_var x))

(****************************************************************************
 *              Functional constructors with position for terms             *
 ****************************************************************************)

let tcoer_p : pos -> term -> kind -> term =
  fun p t k -> in_pos p (TCoer(t,k))

let tvari_p : pos -> term' variable -> term =
  fun p x -> in_pos p (TVari(x))

let tabst_p : pos -> kind option -> (term', term) binder -> term =
  fun p ko b -> in_pos p (TAbst(ko,b))

let tkabs_p : pos -> (kind, term) binder -> term =
  fun p b -> in_pos p (TKAbs(b))

let toabs_p : pos -> (ordinal, term) binder -> term =
  fun p b -> in_pos p (TOAbs(b))

let tappl_p : pos -> term -> term -> term =
  fun p t u -> in_pos p (TAppl(t,u))

let treco_p : pos -> (string * term) list -> term =
  fun p fs -> in_pos p (TReco(fs))

let tproj_p : pos -> term -> string -> term =
  fun p t l -> in_pos p (TProj(t,l))

let tcons_p : pos -> string -> term -> term =
  fun p c t -> in_pos p (TCons(c,t))

let tcase_p : pos -> term -> (string * term) list -> term option -> term =
  fun p t cs cd -> in_pos p (TCase(t,cs,cd))

let tdefi_p : pos -> value_def -> term =
  fun p v -> in_pos p (TDefi(v))

let tprnt_p : pos -> string -> term =
  fun p s -> in_pos p (TPrnt(s))

let tfixy_p : pos -> bool -> int -> (term', term) binder -> term =
  fun p b n t -> in_pos p (TFixY(b,n,t))

(****************************************************************************)
(** {0                   Smart constructors for terms                     } *)
(****************************************************************************)

let tcoer : pos -> tbox -> kbox -> tbox =
  fun p -> box_apply2 (tcoer_p p)

let tvari : pos -> term' variable -> tbox =
  fun p x -> box_apply (in_pos p) (box_of_var x)

let tabst : pos -> kbox option -> strpos -> (tvar -> tbox) -> tbox =
  fun p ko x f ->
    box_apply2 (tabst_p p) (box_opt ko) (vbind mk_free_tvari x.elt f)

let tkabs : pos -> strpos -> (kvar -> tbox) -> tbox =
  fun p x f ->
    box_apply (tkabs_p p) (vbind mk_free_kvari x.elt f)

let toabs : pos -> strpos -> (ovar -> tbox) -> tbox =
  fun p o f ->
    box_apply (toabs_p p) (vbind mk_free_ovari o.elt f)

let idt : tbox =
  let fn x = box_apply dummy_pos (box_of_var x) in
  tabst dummy_position None (dummy_pos "x") fn

let tappl : pos -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (tappl_p p)

let treco : pos -> (string * tbox) list -> tbox =
  fun p fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> treco_p p fs) (box_list fs)

let tproj : pos -> tbox -> string -> tbox =
  fun p t l -> box_apply (fun t -> tproj_p p t l) t

let tcase : pos -> tbox -> (string * tbox) list -> tbox option -> tbox =
  fun p t cs cd ->
    let aux (c,t) = box_apply (fun t -> (c,t)) t in
    box_apply3 (tcase_p p) t (box_list (List.map aux cs)) (box_opt cd)

let tcons : pos -> string -> tbox -> tbox =
  fun p c t -> box_apply (fun t -> tcons_p p c t) t

let tdefi : pos -> value_def -> tbox =
  fun p vd -> box (tdefi_p p vd)

let tprnt : pos -> string -> tbox =
  fun p s -> box (tprnt_p p s)

let tfixy : pos -> bool -> int -> strpos -> (tvar -> tbox) -> tbox =
  fun p b n x f -> box_apply (tfixy_p p b n)
                    (vbind mk_free_tvari x.elt f)

(* Build a constant. Useful during typing. *)
let tcnst : (term', term) binder -> kind -> kind -> term' =
  fun s a b -> TCnst(s,a,b)

let generic_tcnst : kind -> kind -> term =
  fun a b ->
    let f = bind mk_free_tvari "x" (fun x -> box_apply dummy_pos x) in
    dummy_pos (TCnst(unbox f,a,b))
