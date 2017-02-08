
(** Abstract syntax tree. Definition of the internal representation of SubML's
    types, terms and syntactic ordinals in an abstract syntax tree (AST).
    @author Christophe Raffalli <christophe.raffalli\@univ-savoie.fr>
    @author Rodolphe Lepigre <rodolphe.lepigre\@univ-savoie.fr> *)

open Bindlib
open Subset
open Format
open LibTools

(****************************************************************************)
(** {2 Main types for the AST}                                              *)
(****************************************************************************)

(** Occurence markers for variables. *)
type occur =
  | Non (** The variable does not occur. *)
  | Pos of bool (** The variable occurs only positively. *)
  | Neg of bool (** The variable occurs only negatively. *)
  | All (** The variable occurs both positively and negatively. *)
  | Reg of int * occur array
  (** Special constructor for constructing the variance of definitions. *)

(** Ast of kinds (or types). *)
type kind =
  | KVari of kind var             (** Free type variable. *)
  | KFunc of kind * kind          (** Arrow type. *)
  | KProd of (string * kind) list (** Record (or product) type. *)
  | KDSum of (string * kind) list (** Sum (of Variant) type. *)
  | KKAll of kkbinder             (** Universal quantifier over a type. *)
  | KKExi of kkbinder             (** Corresponding existential quantifier. *)
  | KOAll of okbinder             (** Universal quantifier over an ordinal. *)
  | KOExi of okbinder             (** Corresponding existential quantifier. *)
  | KFixM of ordi * kkbinder      (** Least fixpoint with ordinal size. *)
  | KFixN of ordi * kkbinder      (** Greatest fixpoint with ordinal size. *)
  | KDefi of kdefi                (** User-defined type with its arguments. *)

  (** Witnesses (a.k.a. epsilons) used with quantifiers over types. Note that
     the boolean is [true] if the term is closed. This is a necessary
     optimisation to keep physical equality and therefore avoid
     traversing witnesses in comparison tests *)

  | KUCst of term * kkbinder * bool (** Universal witness. *)
  | KECst of term * kkbinder * bool (** Existential witness. *)

  (** Special constructors (not accessible to user). *)

  | KUVar of kuvar * ordi array   (** Unification variable. *)
  | KMRec of ordi set * kind      (** Ordinal conjunction. FIXME wrong name *)
  | KNRec of ordi set * kind      (** Ordinal disjunction. FIXME wrong name *)
  | KPrnt of kprint               (** Special pretty-printing constructor. *)

(** [Bindlib] binder for an ordinal in a kind. *)
and okbinder = (ordi, kind) binder

(** [Bindlib] binder for a kind in a kind. *)
and kkbinder = (kind, kind) binder

(** Fully applied type definition with its ordinal and kind arguments. *)
and kdefi = kdef * ordi array * kind array

(** Pretty-printing markers for free variables and dot-projection. *)
and kprint =
  | FreeVr of string           (** Used to print a variable. *)
  | DotPrj of string * string  (** Used to print a dot projection. *)

(** User-defined type with ordinal and kind parameters. *)
and kdef =
  { tdef_name      : string      (** Name of the type constructor. *)
  ; tdef_tex_name  : string      (** LateX Name of the type constructor. *)
  ; tdef_oarity    : int         (** Number of ordinal parameters. *)
  ; tdef_karity    : int         (** Number of type parameters. *)
  ; tdef_ovariance : occur array (** Variance of the ordinal parameters *)
  ; tdef_kvariance : occur array (** Variance of the type parameters *)
  ; tdef_value     : okmkbinder  (** Definition of the constructor. *) }

(** [Bindlib] type for a kind parametrised by ordinals and kinds. *)
and okmkbinder = kind from_kinds from_ordis

(** [Bindlib] type for a term parametrised by ordinals and kinds. *)
and okmtbinder = term from_kinds from_ordis

(** General [Bindlib] types for ['a] parametrised by ordinals. *)
and 'a from_ordis  = (ordi, 'a) mbinder

(** General [Bindlib] types for ['a] parametrised by kinds. *)
and 'a from_kinds = (kind  , 'a) mbinder

(** Unification variable type managed using a union-find algorithm. *)
and ('a,'b) uvar =
  { uvar_key   : int                      (** Unique key (or UID). *)
      (** Value of the variable, or some information *)
  ; uvar_state   : ('a, 'b) uvar_state ref
  ; uvar_arity : int                      (** Arity of the variable. *) }

and ('a, 'b) uvar_state = Set of 'a from_ordis | Unset of 'b

(** Unification variable for a kind. *)
and kuvar = (kind, kuvar_state) uvar

(** State of a unification variable for kinds, useful for the inference of sum
    types and product types. *)
and kuvar_state =
  | Free                                    (** No constraint. *)
  | DSum of (string * kind from_ordis) list (** Has the given constructors. *)
  | Prod of (string * kind from_ordis) list (** Has the given fields. *)

(** Abstract syntax tree for ordinals. *)
and ordi =
  (* Main type constructors. *)

  | OVari of ordi var (** Free ordinal variable. *)
  | OConv             (** Biggest ordinal (makes fixpoints converge). *)
  | OSucc of ordi     (** Succesor of an ordinal. *)

  (* Witnesses (a.k.a. epsilons) used in the μl and νr rules. [OLess(o,w)] is
     an ordinal (strictly) smaller that [o] such that [w] holds, or zero if no
     such ordinal exists. Contrary to kind witnesses, ordinal witnesses are
     not accessible to the user. *)

  | OLess of ordi * ord_wit (** Ordinal witness. *)

  | OUVar of ouvar * ordi array (** Unification variables for ordinals. *)
  | OVars of string (** for printing only *)

(** Unification variable for an ordinal. *)
and ouvar = (ordi, (ordi from_ordis) option * (ordi from_ordis) option) uvar

(** Ordinal constraints carried by ordinal witnesses. *)
and ord_wit =
  | In     of term * (ordi, kind) binder
  (** [OLess(o',In(t,f))] refers to an ordinal [o] smaller than [o'] and such
     that [t] has type [Bindlib.subst f o]. *)

  | NotIn  of term * (ordi, kind) binder
  (** [OLess(o',NotIn(t,f))] refers to an ordinal [o] smaller than [o'] and
     such that [t] does not have type [Bindlib.subst f o]. *)

  | Gen    of int * schema
  (** the i-th member of a counter example to e schema *)

(** Abstract syntax tree for terms, with a source code position. *)
and term = term' Pos.loc

(** syntactic sugar from parsing *)
and sugar =
  | SgNop
  | SgNil
  | SgCns
  | SgRec of string list
  | SgTpl of int

(** Abstract syntax tree for terms. *)
and term' =
  (* Main term constructors. *)
  | TVari of term' var                                  (** Free λ-variable. *)
  | TAbst of kind option * (term', term) binder * sugar (** λ-abstraction. *)
  | TAppl of term * term                                (** Application. *)
  | TReco of (string * term) list                       (** Record. *)
  | TProj of term * string                              (** Projection. *)
  | TCons of string * term                              (** Variant. *)
  | TCase of term * (string * term) list * term option  (** Case analysis. *)
  | TDefi of tdef                                       (** Defined term. *)
  | TFixY of bool option * int * (term', term) binder
  (** Fixpoint combinator. the integer is an indications for the termination
      checker. It indicates the number of unrolling to build the induction
      hypothesis. The boolean indicates if contravariant Conv must not be
      replaced by ordinal parameters *)

  (* Type annotations. They are not part of the semantics, and they are only
     used to guide the type-checking algorithm. *)

  | TCoer of term * kind                               (** Type coercion. *)
  | TMLet of okmkbinder * term option * okmtbinder
  (** Matching over a type to access the typing environment. *)

  (* Special constructors (not accessible to user). *)

  | TCnst of (term', term) binder * kind * kind
  (** Witness (a.k.a. epsilon). [Cnst(f,a,b)] denotes a term [u] of type [a]
      such that [Bindlib.subst f u] does not have type [b]. *)
  | TPrnt of string
  (** Print a message on the screen. Note that this operation performs is a
      side-effect. *)
  | TVars of string
  (** Special pretty printing constructor *)

(** Term definition (user defined term) *)
and tdef =
  { name       : string  (** Name of the term. *)
  ; tex_name   : string  (** Latex name of the term. *)
  ; value      : term    (** Evaluated term. *)
  ; orig_value : term    (** Original term (not evaluated). *)
  ; ttype      : kind    (** Type of the term. *)
  ; proof      : typ_prf (** Typing proof. *)
  ; calls_graph: Sct.t   (** SCT instance. *) }

(** the type of a general typing judgement, i.e. with
    quantified ordinals *)
and schema =
  { sch_index : Sct.index (** index of the schema in the sct call graph *)
  ; sch_posit : int list  (** the index of positive ordinals *)
  ; sch_relat : (int * int) list (** relation between ordinals *)
  ; sch_judge : (ordi, term_or_kind * kind) mbinder (** judgement *) }

and term_or_kind =
  | SchTerm of (term', term) binder
  | SchKind of kind

(****************************************************************************)
(** {2 Representation of proof trees}                                       *)
(****************************************************************************)

(** Subtyping proof *)
and sub_rule =
  | Sub_Delay  of sub_prf ref
  | Sub_Lower
  | Sub_Func   of sub_prf * sub_prf
  | Sub_Prod   of (string * sub_prf) list
  | Sub_DSum   of (string * sub_prf) list
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
  | Sub_Gen    of schema * (ordi * ordi) list * sub_prf
  | Sub_Ind    of schema
  | Sub_Error  of string
and sub_prf =
  ordi list * term * kind * kind * sub_rule
  (** the integer is referenced by induction hyp ([Sub_Ind]) *)

(** Typing proof *)
and typ_rule =
  | Typ_Coer   of sub_prf * typ_prf
  | Typ_Nope   of typ_prf (* For syntactic sugar *)
  | Typ_Defi   of sub_prf
  | Typ_Prnt   of sub_prf
  | Typ_Cnst   of sub_prf
  | Typ_Func_i of sub_prf * typ_prf
  | Typ_Func_e of typ_prf * typ_prf
  | Typ_Prod_i of sub_prf * typ_prf list
  | Typ_Prod_e of typ_prf
  | Typ_DSum_i of sub_prf * typ_prf
  | Typ_DSum_e of typ_prf * typ_prf list * typ_prf option
  | Typ_YGen   of typ_gen ref
  | Typ_Yufl   of typ_prf
  | Typ_Hole   (* used by dummy_proof below *)
  | Typ_Error  of string
and typ_prf =
  ordi list * term * kind * typ_rule
and typ_gen =
  | Todo
  | Induction of schema * sub_prf
  | Unroll of schema * (ordi * ordi) list * typ_prf

let eq_uvar = fun o1 o2 -> o1.uvar_key = o2.uvar_key
(** Equality on variables *)

(** Used as initial value *)
let dummy_proof = (Pos.none (TReco []), KProd [], Typ_Hole)

(**{2 Unfolding unification variables indirections and definitions.
      Also perform mu/nu contractions} *)

(** This flags controls the merging of consecutive mu and nu
    (true by default disables by --no-contr) *)
let contract_mu = ref true

(** Main shared function *)
let is_set : ('a,'b) uvar -> bool = fun u ->
  match !(u.uvar_state) with
  | Set   _ -> true
  | Unset _ -> false

let is_unset : ('a,'b) uvar -> bool = fun u -> not (is_set u)

let uvar_state :  ('a,'b) uvar -> 'b = fun u ->
   match !(u.uvar_state) with
  | Set   _ -> assert false
  | Unset b -> b

let rec repr : bool -> kind -> kind = fun unfold -> function
  | KUVar({uvar_state = {contents = Set k}; uvar_arity=arity}, os) ->
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
  | KDefi({tdef_value = v}, os, ks) when unfold ->
      repr unfold (msubst (msubst v os) ks)
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
  | OUVar({uvar_state = {contents = Set o}}, os) ->  orepr (msubst o os)
  | OSucc o -> OSucc (orepr o)
  | o -> o

(** {2 Pointer to printing function from "print.ml", to use in debugging } *)

let fprint_term : (bool -> formatter -> term -> unit) ref =
  ref (fun _ -> assert false)

let fprint_kind : (bool -> formatter -> kind -> unit) ref =
  ref (fun _ -> assert false)

let fprint_ordi : (bool -> formatter -> ordi -> unit) ref =
  ref (fun _ -> assert false)

(****************************************************************************)
(** {2 Frequently used types and functions}                                 *)
(****************************************************************************)

(** Value and type environments. *)
type val_env = (string, tdef) Hashtbl.t
type typ_env = (string, kdef ) Hashtbl.t

let typ_env : typ_env = Hashtbl.create 17
let val_env : val_env = Hashtbl.create 17
let verbose : bool ref = ref false

(****************************************************************************)
(** {2 Bindbox type shortcuts}                                              *)
(****************************************************************************)

type tvar = term' var
type tbox = term bindbox

type kvar = kind var
type kbox = kind bindbox

type ovar = ordi var
type obox = ordi bindbox

(** Kind variable management. *)
let mk_free_k : kind var -> kind =
  fun x -> KVari(x)

let new_kvari : string -> kind var =
  new_var mk_free_k

(** Term variable management. *)
let mk_free_tvari : term' var -> term' =
  fun x -> TVari(x)

let new_tvari : string -> term' var =
  new_var mk_free_tvari

(** Ordinal variable management. *)
let mk_free_o : ovar -> ordi =
  fun o -> OVari(o)

let new_ovari : string -> ovar =
  new_var mk_free_o

(****************************************************************************)
(** {2 Smart constructors for ordinals}                                     *)
(****************************************************************************)

let oconv = box OConv

let osucc o = box_apply (fun o -> OSucc o) o
let rec oadd o n = if n <= 0 then o else oadd (OSucc o) (n-1)

let ouvar : ouvar -> obox array -> obox =
  fun u os ->
    box_apply (fun os -> OUVar(u,os)) (box_array os)

let oless_In    = box_apply3 (fun o t k -> OLess(o, In(t,k)))
let oless_NotIn = box_apply3 (fun o t k -> OLess(o,NotIn(t,k)))
let oless_Gen o i s = box_apply2 (fun o s -> OLess(o,Gen(i,s))) o s

(****************************************************************************)
(** {2 Smart constructors for kinds}                                        *)
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
    box_apply (fun b -> KKAll(b)) (vbind mk_free_k x f)

let kkexi : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KKExi(b)) (vbind mk_free_k x f)

let koall : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KOAll(b)) (vbind mk_free_o x f)

let koexi : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KOExi(b)) (vbind mk_free_o x f)

let kdefi : kdef -> obox array -> kbox array -> kbox =
  fun td os ks ->
    let fn td os ks = KDefi(td,os,ks) in
    box_apply3 fn (box td) (box_array os) (box_array ks)

let kfixn : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_k x f in
    box_apply2 (fun o b -> KFixN(o,b)) o b

let kfixm : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_k x f in
    box_apply2 (fun o b -> KFixM(o,b)) o b

let kuvar : kuvar -> obox array -> kbox =
  fun u os ->
    box_apply (fun os -> KUVar(u,os)) (box_array os)

let kucst : string -> tbox -> (kvar -> kbox) -> kbox =
  fun x t f ->
    let b = vbind mk_free_k x f in
    let cl = is_closed t && is_closed b in
    box_apply2 (fun t b -> KUCst(t,b,cl)) t b

let kecst : string -> tbox -> (kvar -> kbox) -> kbox =
  fun x t f ->
    let b = vbind mk_free_k x f in
    let cl = is_closed t && is_closed b in
    box_apply2 (fun t b -> KECst(t,b,cl)) t b

(** Unification variable management. Useful for typing. *)
let (new_kuvar, new_kuvara, reset_all, new_ouvara, new_ouvar) =
  let c = ref 0 in
  let new_kuvara ?(state=Free) n : kuvar = {
    uvar_key = (incr c; !c);
    uvar_state = ref (Unset state);
    uvar_arity = n
  } in
  let new_kuvar ?(state=Free) () =
    KUVar(new_kuvara ~state 0, [||])
  in
  let reset_all () = c := 0 in
  let new_ouvara ?lower ?upper n : ouvar = {
    uvar_key = (incr c; !c);
    uvar_state = ref (Unset (lower, upper));
    uvar_arity = n;
  } in
  let new_ouvar ?lower ?upper () =
    OUVar(new_ouvara ?lower ?upper 0, [||])
  in
  (new_kuvar, new_kuvara, reset_all, new_ouvara, new_ouvar)

(****************************************************************************)
(** {2 Smart constructors for terms}                                        *)
(****************************************************************************)

let tcoer : Pos.popt -> tbox -> kbox -> tbox =
  fun p ->
    box_apply2 (fun t k -> Pos.make p (TCoer(t,k)))

let tvari : Pos.popt -> term' var -> tbox =
  fun p x ->
    box_apply (Pos.make p) (box_of_var x)

let tabst : Pos.popt -> kbox option -> Pos.strloc -> sugar ->
            (tvar -> tbox) -> tbox =
  fun p ko x s f ->
    let b = vbind mk_free_tvari Pos.(x.elt) f in
    box_apply2 (fun ko b -> Pos.make p (TAbst(ko,b,s))) (box_opt ko) b

let tappl : Pos.popt -> tbox -> tbox -> tbox =
  fun p ->
    box_apply2 (fun t u -> Pos.make p (TAppl(t,u)))

let treco : Pos.popt -> (string * tbox) list -> tbox =
  fun p fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> Pos.make p (TReco(fs))) (box_list fs)

let tproj : Pos.popt -> tbox -> string -> tbox =
  fun p t l ->
    box_apply (fun t -> Pos.make p (TProj(t,l))) t

let tcase : Pos.popt -> tbox -> (string * tbox) list -> tbox option -> tbox =
  fun p t cs cd ->
    let fn (c,t) = box_apply (fun t -> (c,t)) t in
    let cs = box_list (List.map fn cs) in
    box_apply3 (fun t cs cd -> Pos.make p (TCase(t,cs,cd))) t cs (box_opt cd)

let tcons : Pos.popt -> string -> tbox -> tbox =
  fun p c t ->
    box_apply (fun t -> Pos.make p (TCons(c,t))) t

let tdefi : Pos.popt -> tdef -> tbox =
  fun p vd ->
    box (Pos.make p (TDefi(vd)))

let tprnt : Pos.popt -> string -> tbox =
  fun p s ->
    box (Pos.make p (TPrnt(s)))

let tfixy : Pos.popt -> int -> Pos.strloc -> (tvar -> tbox) -> tbox =
  fun p n x f ->
    let b = vbind mk_free_tvari Pos.(x.elt) f in
    box_apply (fun b -> Pos.make p (TFixY(None,n,b))) b

let tmlet : Pos.popt -> string array -> string array ->
            (ovar array -> kvar array -> kbox) -> tbox option ->
            (ovar array -> kvar array -> tbox) -> tbox =
  fun p os ks kf x tf ->
    let k = mvbind mk_free_o os (fun x -> mvbind mk_free_k ks (kf x)) in
    let o = mvbind mk_free_o os (fun x -> mvbind mk_free_k ks (tf x)) in
    box_apply3 (fun b x t -> Pos.make p (TMLet(b,x,t))) k (box_opt x) o

let tcnst : (term', term) binder -> kbox -> kbox -> tbox =
  (* NOTE a term witness needs to be closed. *)
  fun s a b ->
    assert (is_closed a && is_closed b);
    box_apply Pos.none (box_apply2 (fun a b -> TCnst(s,a,b)) a b)

(****************************************************************************)
(** {2 Definition of common types and terms}                                *)
(****************************************************************************)

let bot : kind =
  unbox (kkall "X" (fun x -> box_of_var x))

let top : kind =
  unbox (kkexi "X" (fun x -> box_of_var x))

let idt : tbox =
  let fn x = box_apply Pos.none (box_of_var x) in
  tabst None None (Pos.none "x") SgNop fn

let generic_tcnst : kbox -> kbox -> tbox =
  fun a b ->
    let f = bind mk_free_tvari "x" (fun x -> box_apply Pos.none x) in
    tcnst (unbox f) a b

(****************************************************************************)
(** {2 Syntactic sugars}                                                    *)
(****************************************************************************)

(** dot projection: computing the witness *)
let rec do_dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in
     if binder_name f = s then c else do_dot_proj t (subst f c) s
  | k ->
     failwith "Illegal dot projection"

(** dot projection: we compute the projection
    if t is an epsilon or a definition.
    We also deal with a special case for printing !) *)
let dot_proj : tbox -> string -> kbox = fun t s ->
  let fn t = match Pos.(t.elt) with
    | TDefi(d) -> do_dot_proj t d.ttype s
    | TCnst(_,a,_) -> do_dot_proj t a s
    | TVars x -> KPrnt (DotPrj(x,s)) (** printing only *)
    | _ -> KProd []
  in
  box_apply fn t

(** with clause *)
let rec with_clause : kbox -> string -> kbox -> kbox = fun a s b ->
  let rec fn a b =
    match full_repr a with
    | KKExi(f) ->
       if binder_name f = s then subst f b else begin
         KKExi(binder_from_fun (binder_name f) (fun x ->
           fn (subst f x) b))
       end
    | KKAll(f) ->
       if binder_name f = s then subst f b else begin
         KKAll(binder_from_fun (binder_name f) (fun x ->
           fn (subst f x) b))
       end
    | KFixM(OConv,f) -> fn (subst f (KFixM(OConv,f))) b
    | KFixN(OConv,f) -> fn (subst f (KFixN(OConv,f))) b
    | k       ->
      failwith ("Illegal use of \"with\" on variable "^s^".")
  in
  box_apply2 fn a b

(****************************************************************************)
(** {2 Variance function}                                                   *)
(****************************************************************************)

let combine oa ob =
  match (oa, ob) with
  | (Reg(_), _     )
  | (_     , Reg(_)) -> assert false
  | (Non   , _     ) -> ob
  | (_     , Non   ) -> oa
  | (All   , _     ) -> All
  | (_     , All   ) -> All
  | (Neg _ , Pos _ ) -> All
  | (Pos _ , Neg _ ) -> All
  | (Neg s1, Neg s2) -> Neg (s1 && s2)
  | (Pos s1, Pos s2) -> Pos (s1 && s2)

let compose oa ob =
  match (oa, ob) with
  | (Reg(_), _     )
  | (_     , Reg(_)) -> assert false
  | (Non   , _     ) -> Non
  | (_     , Non   ) -> Non
  | (All   , _     ) -> All
  | (_     , All   ) -> All
  | (Neg s1, Pos s2) -> Neg (s1 && s2)
  | (Pos s1, Neg s2) -> Neg (s1 && s2)
  | (Neg _ , Neg _ ) -> Pos false
  | (Pos s1, Pos s2) -> Pos (s1 && s2)

let compose2 oa ob =
  match oa with
  | Reg(i,a) -> a.(i) <- combine a.(i) ob; Non
  | _        -> compose oa ob

let neg = function
  | Reg(_) -> assert false
  | Neg(_) -> Pos(false)
  | Pos(b) -> Neg(b)
  | o      -> o

let sPos = Pos true
let sNeg = Neg true

let isPos = function Non | Pos _ -> true | _ -> false
let isNeg = function Non | Neg _ -> true | _ -> false
