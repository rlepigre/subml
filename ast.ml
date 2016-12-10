(** {3 Basic definition of the Ast of types and programs } *)

open Bindlib
open Subset
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

(** {2         AST for kinds (or types), ordinals and terms              }*)
type occur =
  (** Occurence markers for variables. *)
  | Non
  (** The variable does not occur. *)
  | Pos
  (** The variable occurs only positively. *)
  | Neg
  (** The variable occurs only negatively. *)
  | All
  (** The variable occurs both positively and negatively. *)
  | Reg of int * occur array
  (** Special constructor for constructing the variance of definitions. *)

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
  | KUCst of term * (kind, kind) binder * bool
  | KECst of term * (kind, kind) binder * bool
  (** Constants (a.k.a. epsilon) - used for subtyping.
      the boolean tells if the term is closed - i.e. no bindlib variables *)
  (* Special constructors (not accessible to user) *)
  | KUVar of kuvar * ordinal array
  (** Unification variables - used for typechecking. *)
  | KMRec of ordinal set * kind
  | KNRec of ordinal set * kind
  (** Ordinal conjunction and disjunction *)

(** Type definition (user defined type). *)
and type_def =
  { tdef_name     : string
  (** Name of the type constructor. *)
  ; tdef_tex_name : string
  (** LateX Name of the type constructor. *)
  ; tdef_oarity   : int
  (** Number of ordinal parameters. *)
  ; tdef_karity   : int
  (** Number of type parameters. *)
  ; tdef_ovariance : occur array
  (** Variance of the ordinal parameters *)
  ; tdef_kvariance : occur array
  (** Variance of the type parameters *)
  ; tdef_value    : kind from_kinds from_ords
  (** Definition of the constructor. *) }

and 'a from_ords  = (ordinal, 'a) mbinder
(** general bindlib types for 'a parametrised by ordinals *)
and 'a from_kinds = (kind  , 'a) mbinder
(** general bindlib types for 'a parametrised by types *)

(** Unification variable identified by a key and possibly a value. *)
and ('a,'b) uvar =
  { uvar_key : int
  (* Unique key identifying the variable. *)
  ; uvar_val : 'a from_ords option ref
  (** Value of the variable managed as in a union-find algorithm. *)
  ; uvar_state : 'b
  (** user extra field *)
  ; uvar_arity : int
  (** arity of the unification variables *)
  }

and kuvar = (kind, kuvar_state ref) uvar
(** unification variables for types *)

and kuvar_state =
  (** state of a type variables, use to infer sum and product types *)
  | Free
  | Sum  of (string * kind from_ords) list
  | Prod of (string * kind from_ords) list

(** Abstract syntax tree for ordinals. *)
and ordinal =
  | OConv
  (** Ordinal large enough to ensure convergence of all fixpoints. *)
  | OSucc of ordinal
  (** Succesor *)
  | OLess of ordinal * ord_wit
  (** Ordinal created by the μl and νr rules. OLess(o,w) means
      an ordinal less that o such that w holds. zero is
      this does not exists *)
  | OUVar of ouvar * ordinal array
  (** Unification variables for ordinals. *)
  | OVari of ordinal variable
  (** Ordinal variable. *)

and ouvar = (ordinal, (ordinal from_ords) option * (ordinal from_ords) option) uvar

(** ordinal constraints to build above [OLess] witness *)
and ord_wit =
  | In     of term * (ordinal, kind) binder
  (** OLess(o',In(t,f)) means o < o' s.t. t in f(o) *)
  | NotIn  of term * (ordinal, kind) binder
  (** OLess(o',In(t,f)) means o < o' s.t. t not in f(o) *)
  | Gen    of int * (int * int) list * (kind * kind) from_ords
  (** If o_i = OLess(o'_i,Gen(i,rel,(o |-> k1,k2)))
      means o_1 < o'_1, ..., o_n < o'_n s.t.
      - (o_i < o_j) if (i,j) in rel
      - and k1(o_1,\dots,o_n) < k2(o_1,\dots,o_n) is false *)

(** Abstract syntax tree for terms, all indexed with position *)
and term = term' position

and term' =
  (** {2 Main term constructors } ****)
  | TVari of term' variable
  (** Free λ-variable. *)
  | TAbst of kind option * (term', term) binder
  (** λ-abstraction. *)
  | TAppl of term * term
  (** Application. *)
  | TReco of (string * term) list
  (** Record. *)
  | TProj of term * string
  (** Projection. *)
  | TCons of string * term
  (** Variant. *)
  | TCase of term * (string * term) list * term option
  (** Case analysis. *)
  | TDefi of value_def
  (** User-defined term. *)
  | TPrnt of string
  (** Print a string (side effect) and behave like the term. *)
  | TFixY of bool * int * (term', term) binder
  (** Fixpoint combinator, the boolean and integer are indications for the
      termination checker:
      - the boolean enable subsumption of induction hypothesis
      - the integer indicates the number of unrolling to build
        the induction hypothesis *)
  | TCoer of term * kind
  (** Type coercion: not used in the semantics, only used for type-checking *)
  | TKAbs of (kind, term) binder
  (** Lambda on a type, not used in the semantics, allow to introduce variables
      to write coercion *)
  | TOAbs of (ordinal, term) binder
  (** Lambda on an ordinal, as above *)
  (** {2 Special constructors (not accessible to user) } **)
  | TCnst of (term', term) binder * kind * kind * bool
  (** Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness u (i.e. a term)
     that u has type A and such that t[u] is not in B. *)

(** Term definition (user defined term) *)
and value_def =
  { name       : string      (** Name of the term. *)
  ; tex_name   : string      (** Latex name of the term. *)
  ; value      : term        (** Evaluated term. *)
  ; orig_value : term        (** Original term (not evaluated). *)
  ; ttype      : kind        (** Type of the term. *)
  ; proof      : typ_prf     (** Typing proof. *)
  ; calls_graph: Sct.call_table (** SCT instance. *) }

(** {2 Definition of the ast for proof trees. } *)

(** Subtyping proof *)
and sub_rule =
  | Sub_Delay  of sub_prf ref
  | Sub_Lower
  | Sub_Func   of sub_prf * sub_prf
  | Sub_Prod   of (string * sub_prf) list
  | Sub_DSum   of (string * sub_prf) list
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
  | Sub_Ind    of Sct.index
  | Sub_Error  of string
and sub_prf =
  term * kind * kind * Sct.index option * sub_rule
  (** the integer is referenced by induction hyp ([Sub_Ind]) *)

(** Typing proof *)
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
  | Typ_TFix   of (Sct.index * typ_prf) ref
  | Typ_YH     of Sct.index * sub_prf
  | Typ_Hole   (* used by dummy_proof below *)
  | Typ_Error  of string
and typ_prf =
  term * kind * typ_rule

(** Used as initial value *)
let dummy_proof = (dummy_pos (TReco []), KProd [], Typ_Hole)

(**{2 Unfolding unification variables indirections and definitions.
      Also perform mu/nu contractions} *)

(** This flags controls the merging of consecutive mu and nu
    (true by default disables by --no-contr) *)
let contract_mu = ref true

(** Main shared function *)
let rec repr : bool -> kind -> kind = fun unfold -> function
  | KUVar({uvar_val = {contents = Some k}; uvar_arity=arity}, os) ->
     assert (mbinder_arity k = arity);
     assert (Array.length os = arity);
     repr unfold (msubst k os)
  | KFixM(OConv,f) when !contract_mu && is_mu unfold f ->
     let aux x =
       match repr unfold (subst f x) with
       | KFixM(OConv,g) -> subst g x
       | _              -> assert false (* Unreachable. *)
     in
     let f = binder_from_fun (binder_name f) aux in
     let a' = KFixM(OConv, f) in
     repr unfold a'
  | KFixN(OConv,f) when !contract_mu && is_nu unfold f ->
     let aux x =
       match repr unfold (subst f x) with
       | KFixN(OConv,g) -> subst g x
       | _              -> assert false (* Unreachable. *)
     in
     let f = binder_from_fun (binder_name f) aux in
     let a' = KFixN(OConv, f) in
     repr unfold a'
  | KDefi({tdef_value = v}, os, ks) when unfold -> repr unfold (msubst (msubst v os) ks)
  | KMRec(p,k) when Subset.is_empty p -> repr unfold k
  | KNRec(p,k) when Subset.is_empty p -> repr unfold k
  | k -> k

and is_mu unfold f = !contract_mu &&
  match repr unfold (subst f (KProd [])) with KFixM(OConv,_) -> true
  | _ -> false

and is_nu unfold f = !contract_mu &&
  match repr unfold (subst f (KProd [])) with KFixN(OConv,_) -> true
  | _ -> false

(** The main function: unfold type variables indirections and definitions *)
let full_repr : kind -> kind = fun k -> repr true  k

(** The main function: unfold type variables indirections only *)
let      repr : kind -> kind = fun k -> repr false k

(** Unfold ordinal variables indirections *)
let rec orepr o =
  match o with
  | OUVar({uvar_val = {contents = Some o}}, os) ->  orepr (msubst o os)
  | OSucc o -> OSucc (orepr o)
  | o -> o

(** {2 Pointer to printing function from "print.ml", to use in debugging } *)

let fprint_term : (bool -> formatter -> term -> unit) ref =
  ref (fun _ -> assert false)

let fprint_kind : (bool -> formatter -> kind -> unit) ref =
  ref (fun _ -> assert false)

let fprint_ordinal : (bool -> formatter -> ordinal -> unit) ref =
  ref (fun _ -> assert false)

let ftry_fold_def : (kind -> kind) ref =
  ref (fun _ -> assert false)

(****************************************************************************)
(** {2               Frequently used types and functions                   }*)
(****************************************************************************)

(** Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

let typ_env : typ_env = Hashtbl.create 17
let val_env : val_env = Hashtbl.create 17
let verbose : bool ref = ref false

(****************************************************************************)
(**{2                     Bindbox type shortcuts.                          }*)
(****************************************************************************)
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

(****************************************************************************)
(**{2                    Smart constructors for ordinals                   }*)
(****************************************************************************)

let oconv = box OConv

let osucc o = box_apply (fun o -> OSucc o) o
let rec oadd o n = if n <= 0 then o else oadd (OSucc o) (n-1)

let ouvar : ouvar -> obox array -> obox =
  fun u os ->
    box_apply (fun os -> OUVar(u,os)) (box_array os)

let oless_In    = box_apply3 (fun o t k -> OLess(o, In(t,k)))
let oless_NotIn = box_apply3 (fun o t k -> OLess(o,NotIn(t,k)))
let oless_Gen o i rel p = box_apply2 (fun o p -> OLess(o,Gen(i,rel,p))) o p

(****************************************************************************)
(**{2                     Smart constructors for kinds                     }*)
(****************************************************************************)

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

let kdefi : type_def -> obox array -> kbox array -> kbox =
  fun td os ks ->
    let fn td os ks = KDefi(td,os,ks) in
    box_apply3 fn (box td) (box_array os) (box_array ks)

let kfixn : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixN(o,b)) o b

let kfixm : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixM(o,b)) o b

let kuvar : kuvar -> obox array -> kbox =
  fun u os ->
    box_apply (fun os -> KUVar(u,os)) (box_array os)

let kucst : string -> tbox -> (kvar -> kbox) -> kbox =
  fun x t f ->
    let b = vbind mk_free_kvari x f in
    let cl = is_closed t && is_closed b in
    box_apply2 (fun t b -> KUCst(t,b,cl)) t b

let kecst : string -> tbox -> (kvar -> kbox) -> kbox =
  fun x t f ->
    let b = vbind mk_free_kvari x f in
    let cl = is_closed t && is_closed b in
    box_apply2 (fun t b -> KECst(t,b,cl)) t b

(** Unification variable management. Useful for typing. *)
let (new_kuvar, new_kuvara, reset_all, new_ouvara, new_ouvar) =
  let c = ref 0 in
  let new_kuvara ?(state=Free) n : kuvar = {
    uvar_key = (incr c; !c);
    uvar_val = ref None;
    uvar_state = ref state;
    uvar_arity = n
  } in
  let new_kuvar ?(state=Free) () =
    KUVar(new_kuvara ~state 0, [||])
  in
  let reset_all () = c := 0 in
  let new_ouvara ?lower ?upper n : ouvar = {
    uvar_key = (incr c; !c);
    uvar_val = ref None;
    uvar_state = (lower, upper);
    uvar_arity = n;
  } in
  let new_ouvar ?lower ?upper () =
    OUVar(new_ouvara ?lower ?upper 0, [||])
  in
  (new_kuvar, new_kuvara, reset_all, new_ouvara, new_ouvar)


(****************************************************************************)
(**{2                     Definition of widely used types                  }*)
(****************************************************************************)

let bot : kind =
  unbox (kkall "X" (fun x -> box_of_var x))

let top : kind =
  unbox (kkexi "X" (fun x -> box_of_var x))

(****************************************************************************)
(**{2              Functional constructors with position for terms         }*)
(****************************************************************************)

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
(** {2                   Smart constructors for terms                      }*)
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
let tcnst : (term', term) binder -> kbox -> kbox -> tbox =
  (* NOTE: the term is always closed *)
  fun s a b ->
    let cl = is_closed a && is_closed b in
    assert cl; (* NOTE: we do not assume a b closed, but check it.
                  indeed, map_term could bind under a TCnst *)
    box_apply dummy_pos (box_apply2 (fun a b -> TCnst(s,a,b,cl)) a b)

let generic_tcnst : kbox -> kbox -> tbox =
  fun a b ->
    let f = bind mk_free_tvari "x" (fun x -> box_apply dummy_pos x) in
    tcnst (unbox f) a b

(****************************************************************************)
(**{2                          variance function                           }*)
(****************************************************************************)

let combine oa ob =
  match (oa, ob) with
  | (Reg(_), _     )
  | (_     , Reg(_)) -> assert false
  | (Non   , _     ) -> ob
  | (_     , Non   ) -> oa
  | (All   , _     ) -> All
  | (_     , All   ) -> All
  | (Neg   , Pos   ) -> All
  | (Pos   , Neg   ) -> All
  | (Neg   , Neg   ) -> Neg
  | (Pos   , Pos   ) -> Pos

let compose oa ob =
  match (oa, ob) with
  | (Reg(_), _     )
  | (_     , Reg(_)) -> assert false
  | (Non   , _     ) -> Non
  | (_     , Non   ) -> Non
  | (All   , _     ) -> All
  | (_     , All   ) -> All
  | (Neg   , Pos   ) -> Neg
  | (Pos   , Neg   ) -> Neg
  | (Neg   , Neg   ) -> Pos
  | (Pos   , Pos   ) -> Pos

let compose2 oa ob =
  match oa with
  | Reg(i,a) -> a.(i) <- combine a.(i) ob; Non
  | _        -> compose oa ob

let neg = function
  | Reg(_) -> assert false
  | Neg    -> Pos
  | Pos    -> Neg
  | o      -> o
