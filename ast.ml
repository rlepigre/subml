open Bindlib

exception Stopped

let handle_stop : bool -> unit =
  let open Sys in function
  | true  -> set_signal sigint (Signal_handle (fun i -> raise Stopped))
  | false -> set_signal sigint Signal_default

let map_opt : ('a -> 'b) -> 'a option -> 'b option = fun f o ->
  match o with None -> None | Some e -> Some (f e)

let from_opt : 'a option -> 'a -> 'a = fun o d ->
  match o with None -> d | Some e -> e

let eq_assoc : ('b -> 'b -> bool) -> ('a * 'b) list -> ('a * 'b) list
                 -> bool = fun eq l1 l2 ->
  List.for_all (fun (k,_) -> List.mem_assoc k l2) l1 &&
  List.for_all (fun (k,_) -> List.mem_assoc k l1) l2 &&
  List.for_all (fun (k,e1) -> eq e1 (List.assoc k l2)) l1

(****************************************************************************
 *                     Source code position management                      *
 ****************************************************************************)

module Location =
  struct
    open Lexing

    type t =
      { loc_start : position
      ; loc_end   : position
      ; loc_ghost : bool }

    let in_file pos_fname =
      let loc = { pos_fname ; pos_lnum = 1 ; pos_bol = 0 ; pos_cnum = -1 } in
      { loc_start = loc ; loc_end = loc ; loc_ghost = true }

    let none = in_file "_none_"

    let locate str1 pos1 str2 pos2 =
      let loc_start = Input.lexing_position str1 pos1 in
      let loc_end   = Input.lexing_position str2 pos2 in
      { loc_start ; loc_end ; loc_ghost = false }
end

type pos = Location.t

type 'a position = { elt : 'a ; pos : pos }

let in_pos : pos -> 'a -> 'a position =
  fun p e -> { elt = e; pos = p }

let dummy_position : pos = Location.none

let dummy_pos : 'a -> 'a position = fun e -> in_pos dummy_position e

type strpos = string position

(****************************************************************************
 *              AST for kinds (or types), ordinals and terms                *
 ****************************************************************************)

(* Occurence markers for variables. *)
type occur =
  (* The variable does not occur. *)
  | Non
  (* The variable occurs only positively. *)
  | Pos
  (* The variable occurs only negatively. *)
  | Neg
  (* The variable occurs both positively and negatively. *)
  | All
  (* The variable occurs under an epsilon witness (special case). *)
  | Eps
  (* Special constructor for constructing the variance of definitions. *)
  | Reg of int * occur array * int array

(* Ast of kinds (or types). *)
type kind =
  (**** Main type constructors ****)
  (* Type variable. *)
  | KVari of kind variable
  (* Function type: A ⇒ B. *)
  | KFunc of kind * kind
  (* Product (record) type: {l1 : A1 ; ... ; ln : An}. *)
  | KProd of (string * kind) list
  (* Sum (variant) type: [C1 of A1 | ... | Cn of An]. *)
  | KDSum of (string * kind) list
  (* Quantifiers over a type: ∀/∃X A. *)
  | KKAll of (kind, kind) binder
  | KKExi of (kind, kind) binder
  (* Quantifiers over an ordinal: ∀/∃o A. *)
  | KOAll of (ordinal, kind) binder
  | KOExi of (ordinal, kind) binder
  (* Least and greatest fixpoint: μα X A, να X A. *)
  | KFixM of ordinal * (kind, kind) binder
  | KFixN of ordinal * (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | KDefi of type_def * kind array
  (* Dot projection t.X. *)
  | KDPrj of term * string
  (* With clause A with X = B. *)
  | KWith of kind * (string * kind)
  (**** Special constructors (not accessible to user) ****)
  (* Constants (a.k.a. epsilon) - used for subtyping. *)
  | KUCst of term * (kind, kind) binder
  | KECst of term * (kind, kind) binder
  (* Unification variables - used for typechecking. *)
  | KUVar of uvar
  (* Integer tag for comparing kinds. *)
  | KTInt of int

(* Type definition (user defined type). *)
and type_def =
  (* Name of the type constructor. *)
  { tdef_name     : string
  ; tdef_tex_name : string
  (* Arity of the constructor. *)
  ; tdef_arity    : int
  ; tdef_variance : occur array
  ; tdef_depth    : int array
  (* Definition of the constructor. *)
  ; tdef_value    : (kind, kind) mbinder }

(* Unification variable identified by a key and possibly a value. *)
and uvar =
  (* Unique key identifying the variable. *)
  { uvar_key : int
  (* Value of the variable managed as in a union-find algorithm. *)
  ; uvar_val : kind option ref
  ; uvar_hook : (kind -> unit) ref
  ; uvar_state : uvar_state ref }

and uvar_state = Free | Sum | Prod

(* Abstract syntax tree for ordinals. *)
and ordinal =
  (* Ordinal large enough to ensure convergence of all fixpoint. *)
  | OConv
  (* Unification variables for ordinals. *)
  | OUVar of ordinal option * ordinal option ref
  (* Ordinal created by the μl and νr rules. *)
  | OLess of ordinal * ord_wit
  (* Maximum of a list of ordinals. *)
  | OMaxi of ordinal list
  (* Ordinal variable. *)
  | OVari of ordinal variable
  (* Integer tag used in decompose / recompose. *)
  | OTInt of int
and ord_wit =
  | In     of term * (ordinal, kind) binder
  | NotIn  of term * (ordinal, kind) binder

(* Abstract syntax tree for terms. *)
and term = term' position
and term' =
  (**** Main term constructors ****)
  (* Type coercion. *)
  | TCoer of term * kind
  (* Free λ-variable. *)
  | TVari of term variable
  (* λ-abstraction. *)
  | TAbst of kind option * (term, term) binder
  (* Application. *)
  | TAppl of term * term
  (* Record. *)
  | TReco of (string * term) list
  (* Projection. *)
  | TProj of term * string
  (* Variant. *)
  | TCons of string * term
  (* Case analysis. *)
  | TCase of term * (string * term) list
  (* User-defined term. *)
  | TDefi of value_def
  (* Print a string (side effect) and behave like the term. *)
  | TPrnt of string
  (* Fixpoint combinator. *)
  | TFixY of kind option * (term,term) binder
  (* Lambda on a type, semantics via epsilon *)
  | TKAbs of (kind, term) binder
  (* Lambda on an ordinal, semantics via epsilon *)
  | TOAbs of (ordinal, term) binder
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | TCnst of ((term, term) binder * kind * kind)
  (* Specific witness for recursive definitions. *)
  | TCstY of ((term, term) binder * kind)
  (* Integer tag. *)
  | TTInt of int

(* Term definition (user defined term) *)
and value_def =
  { name       : string      (* Name of the term. *)
  ; tex_name   : string      (* Latex name of the term. *)
  ; value      : term        (* Evaluated term. *)
  ; orig_value : term        (* Original term (not evaluated). *)
  ; ttype      : kind        (* Type of the term. *)
  ; proof      : typ_prf     (* Typing proof. *)
  ; calls_graph: Sct.calls_graph } (* SCT instance. *)

and srule_name = NUseInd of int | NRefl | NArrow | NSum | NProd
  | NAllLeft | NAllRight | NExistsLeft | NExistsRight | NMuLeft
  | NMuRightInf | NNuLeftInf | NNuRight | NMuRight | NNuLeft
  | NUnknown | NProjLeft | NProjRight | NWithRight | NWithLeft

and typ_jdg = term * kind
and sub_jdg = term * kind * kind

and sub_rule =
  | Sub_Dummy
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
  | Sub_Ind    of int
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
  | Typ_DSum_e of typ_prf * typ_prf list
  | Typ_Y      of int * sub_prf * sub_prf * typ_prf
  | Typ_YH     of int * sub_prf
and typ_prf =
  term * kind * typ_rule




(* Unfolding unification variable indirections. *)
let rec repr : kind -> kind = function
  | KUVar({uvar_val = {contents = Some k}}) -> repr k
  | k                                       -> k

(* Unfolding unification variable indirections and definitions *)
let rec full_repr : kind -> kind = function
  | KUVar({uvar_val = {contents = Some k}}) -> full_repr k
  | KDefi({tdef_value = v}, a)              -> full_repr (msubst v a)
  | k                                      -> k

let rec orepr = function
  | OUVar(_, {contents = Some o})
  | o                             -> o

let set_kuvar v k =
  assert (!(v.uvar_val) = None);
  Timed.(v.uvar_val := Some k);
  !(v.uvar_hook) k;
  Timed.(v.uvar_hook := (fun _ -> ()))

let set_ouvar v o =
  assert(!v = None);
  Timed.(v := Some o)

(* Printing function from "print.ml" *)
let fprint_term : (bool -> out_channel -> term -> unit) ref =
  ref (fun _ -> assert false)

let fprint_kind : (bool -> out_channel -> kind -> unit) ref =
  ref (fun _ -> assert false)

let fprint_ordinal : (bool -> out_channel -> ordinal -> unit) ref =
  ref (fun _ -> assert false)

(****************************************************************************
 *                   Frequently used types and functions                    *
 ****************************************************************************)

(* Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

let typ_env : typ_env = Hashtbl.create 17
let val_env : val_env = Hashtbl.create 17
let verbose : bool ref = ref false

(* Bindbox type shortcuts. *)
type tvar = term variable
type tbox = term bindbox

type kvar = kind variable
type kbox = kind bindbox

type ovar = ordinal variable
type obox = ordinal bindbox

(* Kind variable management. *)
let mk_free_kvari : kind variable -> kind =
  fun x -> KVari(x)

let new_kvari : string -> kind variable =
  new_var mk_free_kvari

(* Term variable management. *)
let mk_free_tvari : pos -> term variable -> term =
  fun p x -> in_pos p (TVari(x))

let new_tvari : pos -> string -> term variable =
  fun p -> new_var (mk_free_tvari p)

let new_tvari' : string -> term variable =
  new_tvari dummy_position

(* Ordinal variable management. *)
let mk_free_ovari : ovar -> ordinal =
  fun o -> OVari(o)

let new_ovari : string -> ovar =
  new_var mk_free_ovari

(* sugaring for ordinals *)
let oconv = box OConv

let omaxi l = box_apply (fun o -> OMaxi o) (box_list l)

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

let kdefi : type_def -> kbox array -> kbox =
  fun td ks -> box_apply2 (fun td ks -> KDefi(td,ks)) (box td) (box_array ks)

let kfixn : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixN(o,b)) o b

let kfixm : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_kvari x f in
    box_apply2 (fun o b -> KFixM(o,b)) o b

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = KUVar {
    uvar_key = (incr c; !c);
    uvar_val = ref None;
    uvar_hook = ref (fun k -> ());
    uvar_state = ref Free;
  } in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(* Resset all counters. *)
let reset_all () =
  let reset = [reset_uvar] in
  List.iter (fun x -> x ()) reset

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

let tvari_p : pos -> term variable -> term =
  fun p x -> in_pos p (TVari(x))

let tabst_p : pos -> kind option -> (term, term) binder -> term =
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

let tcase_p : pos -> term -> (string * term) list -> term =
  fun p t cs -> in_pos p (TCase(t,cs))

let tdefi_p : pos -> value_def -> term =
  fun p v -> in_pos p (TDefi(v))

let tprnt_p : pos -> string -> term =
  fun p s -> in_pos p (TPrnt(s))

let tfixy_p : pos -> kind option -> (term, term) binder -> term =
  fun p ko t -> in_pos p (TFixY(ko,t))

let tcnst_p : pos -> ((term, term) binder * kind * kind) -> term =
  fun p c -> in_pos p (TCnst(c))

(****************************************************************************
 *                     Smart constructors for terms                         *
 ****************************************************************************)

let tcoer : pos -> tbox -> kbox -> tbox =
  fun p -> box_apply2 (tcoer_p p)

let tvari : pos -> term variable -> tbox =
  fun p x -> box_of_var x

let tabst : pos -> kbox option -> strpos -> (tvar -> tbox) -> tbox =
  fun p ko x f ->
    box_apply2 (tabst_p p) (box_opt ko) (vbind (tvari_p x.pos) x.elt f)

let tkabs : pos -> strpos -> (kvar -> tbox) -> tbox =
  fun p x f ->
    box_apply (tkabs_p p) (vbind mk_free_kvari x.elt f)

let toabs : pos -> strpos -> (ovar -> tbox) -> tbox =
  fun p o f ->
    box_apply (toabs_p p) (vbind mk_free_ovari o.elt f)

let idt : tbox =
  tabst dummy_position None (dummy_pos "x") (fun x -> box_of_var x)

let tappl : pos -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (tappl_p p)

let treco : pos -> (string * tbox) list -> tbox =
  fun p fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> treco_p p fs) (box_list fs)

let tproj : pos -> tbox -> string -> tbox =
  fun p t l -> box_apply (fun t -> tproj_p p t l) t

let tcase : pos -> tbox -> (string * tbox) list -> tbox =
  fun p t cs ->
    let aux (c,t) = box_apply (fun t -> (c,t)) t in
    box_apply2 (tcase_p p) t (box_list (List.map aux cs))

let tcons : pos -> string -> tbox -> tbox =
  fun p c t -> box_apply (fun t -> tcons_p p c t) t

let tdefi : pos -> value_def -> tbox =
  fun p vd -> box (tdefi_p p vd)

let tprnt : pos -> string -> tbox =
  fun p s -> box (tprnt_p p s)

let tfixy : pos -> kbox option -> strpos -> (tvar -> tbox) -> tbox =
  fun p ko x f -> box_apply2 (tfixy_p p) (box_opt ko)
                    (vbind (tvari_p x.pos) x.elt f)

(* Build a constant. Useful during typing. *)
let tcnst : (term, term) binder -> kind -> kind -> term =
  fun s a b -> dummy_pos (TCnst(s,a,b))

let generic_tcnst : kind -> kind -> term =
  fun a b ->
    let f = bind (tvari_p dummy_position) "x" (fun x -> x) in
    dummy_pos (TCnst(unbox f,a,b))

(****************************************************************************
 *                  Equality of types, terms and ordinals                   *
 ****************************************************************************)

let rec eq_kind : int ref -> kind -> kind -> bool = fun c k1 k2 ->
  let rec eq_kind k1 k2 = k1 == k2 ||
    match (full_repr k1, full_repr k2) with
    | (KVari(x1)   , KVari(x2)   ) -> eq_variables x1 x2
    | (KFunc(a1,b1), KFunc(a2,b2)) -> eq_kind a1 a2 && eq_kind b1 b2
    | (KProd(fs1)  , KProd(fs2)  ) -> eq_assoc eq_kind fs1 fs2
    | (KDSum(cs1)  , KDSum(cs2)  ) -> eq_assoc eq_kind cs1 cs2
    | (KKAll(b1)   , KKAll(b2)   )
    | (KKExi(b1)   , KKExi(b2)   ) -> eq_kbinder c b1 b2
    | (KOAll(b1)   , KOAll(b2)   )
    | (KOExi(b1)   , KOExi(b2)   ) -> eq_obinder c b1 b2
    | (KFixM(o1,f1), KFixM(o2,f2))
    | (KFixN(o1,f1), KFixN(o2,f2)) -> eq_ordinal c o1 o2 && eq_kbinder c f1 f2
    | (KDPrj(t1,s1), KDPrj(t2,s2)) -> s1 = s2 && eq_term c t1 t2
    | (KWith(a1,e1), KWith(a2,e2)) -> let (s1,b1) = e1 and (s2,b2) = e2 in
                                      eq_kind a1 a2 && s1 = s2 && eq_kind b1 b2
    | (KUCst(t1,f1), KUCst(t2,f2))
    | (KECst(t1,f1), KECst(t2,f2)) -> eq_kbinder c f1 f2 && eq_term c t1 t2
    | (KUVar(u1)   , KUVar(u2)   ) -> u1.uvar_key = u2.uvar_key
    | (KTInt(i1)   , KTInt(i2)   ) -> i1 = i2
    | (_          , _          ) -> false
  in
  eq_kind k1 k2

and eq_kbinder c f1 f2 = f1 == f2 ||
  let i = incr c; KTInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_obinder c f1 f2 = f1 == f2 ||
  let i = incr c; OTInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_tbinder c f1 f2 = f1 == f2 ||
  let i = incr c; dummy_pos (TTInt(!c)) in
  eq_term c (subst f1 i) (subst f2 i)

and eq_term : int ref -> term -> term -> bool = fun c t1 t2 ->
  let rec eq_term t1 t2 =
    t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (TCoer(t1,_) , _           ) -> eq_term t1 t2
    | (_           , TCoer(t2,_) ) -> eq_term t1 t2
    | (TDefi(d1)   , _           ) -> eq_term d1.value t2
    | (_           , TDefi(d2)   ) -> eq_term t1 d2.value
    | (TKAbs(f)    , _           ) -> eq_term (subst f (KProd[])) t2
    | (_           , TKAbs(f)    ) -> eq_term t1 (subst f (KProd[]))
    | (TOAbs(f)    , _           ) -> eq_term (subst f (OTInt(-1))) t2
    | (_           , TOAbs(f)    ) -> eq_term t1 (subst f (OTInt(-1)))
    | (TVari(x1)   , TVari(x2)   ) -> eq_variables x1 x2
    | (TAbst(_,f1) , TAbst(_,f2) )
    | (TFixY(_,f1) , TFixY(_,f2) ) -> eq_tbinder c f1 f2
    | (TAppl(t1,u1), TAppl(t2,u2)) -> eq_term t1 t2 && eq_term u1 u2
    | (TReco(fs1)  , TReco(fs2)  ) -> eq_assoc eq_term fs1 fs2
    | (TProj(t1,l1), TProj(t2,l2)) -> l1 = l2 && eq_term t1 t2
    | (TCons(c1,t1), TCons(c2,t2)) -> c1 = c2 && eq_term t1 t2
    | (TCase(t1,l1), TCase(t2,l2)) -> eq_term t1 t2 && eq_assoc eq_term l1 l2
    | (TPrnt(s1)   , TPrnt(s2)   ) -> s1 = s2
    | (TCnst(c1)   , TCnst(c2)   ) -> let (f1,a1,b1) = c1 in
                                      let (f2,a2,b2) = c2 in
                                      eq_tbinder c f1 f2 && eq_kind c a1 a2
                                        && eq_kind c b1 b2
    | (TCstY(f1,a1), TCstY(f2,a2)) -> eq_tbinder c f1 f2 && eq_kind c a1 a2
    | (_           , _           ) -> false
  in eq_term t1 t2

and eq_ordinal : int ref -> ordinal -> ordinal -> bool = fun c o1 o2 ->
  match (orepr o1, orepr o2) with
  | (o1          , o2          ) when o1 == o2 -> true
  | (OConv       , OConv       ) -> true
(*  | (OUVar(o',p) , o           )
  | (o           , OUVar(o',p) ) -> Timed.pure_test (less_ordinal [] c o) o' && (* FIXME *)
    (set_ouvar p o; true)*)
  | (OLess(o1,w1), OLess(o2,w2)) -> eq_ordinal c o1 o2 && eq_ord_wit c w1 w2
  | (OMaxi(l1)   , OMaxi(l2)   ) -> List.for_all (fun o1 ->
                                      List.exists (fun o2 ->
                                        eq_ordinal c o1 o2) l2) l1 &&
                                    List.for_all (fun o1 ->
                                      List.exists (fun o2 ->
                                        eq_ordinal c o1 o2) l1) l2
  | (OTInt n1    , OTInt n2    ) -> n1 = n2
  | (_           , _           ) -> false

and eq_ord_wit c w1 w2 = match w1, w2 with
  | (In(t1,f1)    , In(t2,f2)    )
  | (NotIn(t1,f1) , NotIn(t2,f2) ) -> eq_term c t1 t2 && eq_obinder c f1 f2
  | (_            , _            ) -> false

and leq_ordinal pos c o1 o2 =
  match (orepr o1, orepr o2) with
  | (o1         , o2        ) when eq_ordinal c o1 o2 -> true
  | (_          , OConv     ) -> true
  | (OUVar(None, p), o2     ) -> set_ouvar p o2; true
  | (OUVar(Some o, p), o2   ) -> Timed.pure_test (leq_ordinal pos c o) o2 || (
                                   Timed.pure_test (less_ordinal pos c o2) o &&
                                   (set_ouvar p o2; true))
  | (o1      , OUVar(None,p)) -> set_ouvar p o1; true
  | (o1    , OUVar(Some o,p)) -> Timed.pure_test (less_ordinal pos c o1) o &&
                                 (set_ouvar p o1; true)
  | (OLess(o1,_), o2        ) when List.exists (eq_ordinal c o1) pos -> leq_ordinal pos c o1 o2
  | (OMaxi(l1)  , o2        ) -> List.for_all (fun o1 -> leq_ordinal pos c o1 o2) l1
  | (o1         , OMaxi(l2) ) -> List.exists (fun o2 -> leq_ordinal pos c o1 o2) l2
  | (_          , _         ) -> false

and less_ordinal pos c o1 o2 =
  let o1 = orepr o1 and o2 = orepr o2 in
  match o1 with
  | OLess(o,_) when List.exists (eq_ordinal c o) pos -> leq_ordinal pos c o o2
  | OUVar(Some o,_) -> List.exists (eq_ordinal c o) pos && less_ordinal pos c o o2
  | OMaxi(l1)  -> List.for_all (fun o1 -> less_ordinal pos c o1 o2) l1
  | _          -> false

(* FIXME: normalize elements, sort, eliminate duplicate, hashcons ? *)
let omax = function
  | []  -> assert false
  | [o] -> o
  | l   -> OMaxi l

let eq_kind : kind -> kind -> bool =
  fun k1 k2 -> Timed.pure_test (eq_kind (ref 0) k1) k2

let eq_term : term -> term -> bool =
  fun t1 t2 -> Timed.pure_test (eq_term (ref 0) t1) t2

let eq_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> Timed.pure_test (eq_ordinal (ref 0) t1) t2

let eq_ord_wit : ord_wit -> ord_wit -> bool =
  fun t1 t2 -> Timed.pure_test (eq_ord_wit (ref 0) t1) t2

let leq_ordinal : ordinal list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (leq_ordinal pos (ref 0) t1) t2

let less_ordinal : ordinal list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (less_ordinal pos (ref 0) t1) t2

let eq_head_term t u =
  let rec fn u =
    t == u || eq_term t u ||
    match u.elt with
    | TAppl(u,_)
    | TCase(u,_)
    | TProj(u,_) -> fn u
    | TKAbs(f)   -> fn (subst f (KProd[]))
    | TOAbs(f)   -> fn (subst f (OTInt(-1)))
    | _          -> false
  in fn u

 (***************************************************************************
 *                             mapping on terms                             *
 ****************************************************************************)

let map_term : (kind -> kbox) -> term -> tbox = fun kn t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> tcoer t.pos (fn t) (kn k)
    | TVari(x)    -> box_of_var x
    | TAbst(ko,f) -> let ko = map_opt kn ko in
                     tabst t.pos ko (in_pos t.pos (binder_name f))
                       (fun x -> fn (subst f (dummy_pos (TVari x))))
    | TFixY(ko,f) -> let ko = map_opt kn ko in
                     tfixy t.pos ko (in_pos t.pos (binder_name f))
                       (fun x -> fn (subst f (dummy_pos (TVari x))))
    | TKAbs(f)    -> tkabs t.pos (dummy_pos (binder_name f))
                       (fun x -> fn (subst f (KVari x)))
    | TOAbs(f)    -> toabs t.pos (dummy_pos (binder_name f))
                       (fun x -> fn (subst f (OVari x)))
    | TAppl(a,b)  -> tappl t.pos (fn a) (fn b)
    | TReco(fs)   -> treco t.pos (List.map (fun (s,a) -> (s, fn a)) fs)
    | TProj(a,s)  -> tproj t.pos (fn a) s
    | TCons(s,a)  -> tcons t.pos s (fn a)
    | TCase(a,fs) -> tcase t.pos (fn a) (List.map (fun (s,a) -> (s, fn a)) fs)
    | u           -> box_apply (in_pos t.pos) (box u)
  in fn t

(*****************************************************************
 *              test if a term is normal in CBV                  *
******************************************************************)
let is_normal : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> fn t
    | TVari(x)    -> true
    | TAbst(ko,f) -> true
    | TFixY(ko,f) -> false
    | TKAbs(f)    -> fn (subst f (KProd []))
    | TOAbs(f)    -> fn (subst f (OConv))
    | TAppl(a,b)  -> false
    | TReco(fs)   -> List.for_all (fun (_,t) -> fn t) fs
    | TProj(a,s)  -> false
    | TCons(s,a)  -> fn a
    | TCase(a,fs) -> fn a
    | TDefi(d)    -> fn d.value
    | TCnst _     -> true
    | TCstY _     -> false
    | TPrnt _     -> false
    | TTInt _     -> assert false
  in fn t

(* let is_neutral ...  *)

(****************************************************************************
 *                 Occurence test for unification variables                 *
 ****************************************************************************)

let combine oa ob =
  match (oa, ob) with
  | (Reg(_), _     )
  | (_     , Reg(_)) -> assert false
  | (Non   , _     ) -> ob
  | (_     , Non   ) -> oa
  | (Eps   , _     ) -> Eps
  | (_     , Eps   ) -> Eps
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
  | (Eps   , _     ) -> Eps
  | (_     , Eps   ) -> Eps
  | (All   , _     ) -> All
  | (_     , All   ) -> All
  | (Neg   , Pos   ) -> Neg
  | (Pos   , Neg   ) -> Neg
  | (Neg   , Neg   ) -> Pos
  | (Pos   , Pos   ) -> Pos

let compose2 (oa,da) (ob,db) =
  let o =
    match (oa, ob) with
    | (Reg(i,a,d), p) -> a.(i) <- combine a.(i) p;
                         d.(i) <- min d.(i) (db - da); Non
    | _               -> compose oa ob
  in (o, da + db)

let neg = function
  | Reg(_) -> assert false
  | Neg    -> Pos
  | Pos    -> Neg
  | o      -> o

(* FIXME: should memoize this function, because a lot of sub-term are shared
   and we traverse all constants ... One could also precompute the
   variance of definitions to avoid substitution *)
let uvar_occur : uvar -> kind -> occur = fun {uvar_key = i} k ->
  let kdummy = KProd [] in
  let odummy = OTInt(-42) in
  let rec aux occ acc k =
    match repr k with
    | KVari(x)   -> acc
    | KFunc(a,b) -> aux (neg occ) (aux occ acc b) a
    | KProd(ks)
    | KDSum(ks)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc ks
    | KKAll(f)
    | KKExi(f)   -> aux occ acc (subst f kdummy)
    | KOAll(f)
    | KOExi(f)   -> aux occ acc (subst f odummy)
    | KFixM(o,f)
    | KFixN(o,f) -> aux occ (aux3 acc o) (subst f kdummy)
    | KDPrj(t,_) -> aux2 acc t
    | KWith(a,_) -> aux occ acc a (* FIXME *)
    | KDefi(d,a) ->
       let acc = ref acc in
       Array.iteri (fun i k ->
         acc := aux (compose occ d.tdef_variance.(i)) !acc k) a;
       !acc
    | KUCst(t,f)
    | KECst(t,f) -> let a = subst f kdummy in aux2 (aux Eps acc a) t
    | KUVar(u)   -> if u.uvar_key = i then combine acc occ else acc
    | KTInt(_)   -> assert false
  and aux2 acc t = match t.elt with
    | TCnst(t,k1,k2) -> aux2 (aux Eps (aux Eps acc k1) k2) (subst t (dummy_pos (TReco [])))
    | TCstY(t,k)     -> aux2 (aux Eps acc k) (subst t (dummy_pos (TReco [])))
    | TCoer(t,_)
    | TProj(t,_)
    | TCons(_,t)     -> aux2 acc t
    | TFixY(_,f)
    | TAbst(_,f)     -> aux2 acc (subst f (dummy_pos (TReco [])))
    | TKAbs(f)       -> aux2 acc (subst f (KProd []))
    | TOAbs(f)       -> aux2 acc (subst f (OTInt(-1)))
    | TAppl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | TReco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | TCase(t,l)     -> List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | TVari(_)
    | TDefi(_)
    | TPrnt(_)
    | TTInt(_)       -> acc
  and aux3 acc = function
    | OLess(o,(In(t,f)|NotIn(t,f))) -> aux Eps (aux2 (aux3 acc o) t) (subst f odummy)
    (* we keep this to ensure valid proof when simplifying useless induction
       needed because has_uvar below does no check ordinals *)
    | _             -> acc
  in aux Pos Non k

(****************************************************************************
 *                            lifting of kind                               *
 ****************************************************************************)

let lift_kind : kind -> kind bindbox = fun k ->
  let rec fn k =
      match repr k with
      | KFunc(a,b) -> kfunc (fn a) (fn b)
      | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
      | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KKAll(f)   -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KOAll(f)   -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KOExi(f)   -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KFixM(o,f) -> kfixm (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KFixN(o,f) -> kfixn (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KVari(x)   -> box_of_var x
      | KDefi(d,a) -> kdefi d (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | t          -> box t
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | o -> box o
    in
    fn k

(****************************************************************************
 *                 Binding a unification variable in a type                 *
 ****************************************************************************)

let bind_uvar : uvar -> kind -> (kind, kind) binder = fun {uvar_key = i} k ->
  unbox (bind mk_free_kvari "X" (fun x ->
    let rec fn k =
      match repr k with
      | KFunc(a,b) -> kfunc (fn a) (fn b)
      | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
      | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KKAll(f)   -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KOAll(f)   -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KOExi(f)   -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KFixM(o,f) -> kfixm (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KFixN(o,f) -> kfixn (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KUVar(u)   -> assert(!(u.uvar_val) = None); if u.uvar_key = i then x else box k
      | KVari(x)   -> box_of_var x
      | KDefi(d,a) -> kdefi d (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | t         -> box t
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | o -> box o
    in
    fn k))

(****************************************************************************
 *                 Binding a unification variable in a type                 *
 ****************************************************************************)

let bind_ovar : ordinal option ref -> kind -> (ordinal, kind) binder = fun ov0 k ->
  unbox (bind mk_free_ovari "o" (fun x ->
    let rec fn k =
      match repr k with
      | KFunc(a,b) -> kfunc (fn a) (fn b)
      | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
      | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KKAll(f)   -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KOAll(f)   -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KOExi(f)   -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KFixM(o,f) -> kfixm (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KFixN(o,f) -> kfixn (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KUVar(u)   -> assert(!(u.uvar_val) = None); box k
      | KVari(x)   -> box_of_var x
      | KDefi(d,a) -> kdefi d (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | t         -> box t
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | OUVar(_,ov) -> assert(!ov = None); if ov == ov0 then x else box o
      | o -> box o
    in
    fn k))

(****************************************************************************
 *                    Decomposition type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

let contract_mu = ref true
let is_mu f = !contract_mu &&
  match full_repr (subst f (KProd [])) with KFixM(OConv,_) -> true
  | _ -> false
let is_nu f = !contract_mu &&
  match full_repr (subst f (KProd [])) with KFixN(OConv,_) -> true
  | _ -> false

let decompose : bool -> occur -> kind -> kind ->
                  kind * kind * (int * ordinal) list = fun fix pos k1 k2 ->
  let res = ref [] in
  let i = ref 0 in
  let search o =
    try
      match o with
        OLess _ -> OTInt (List.assq o !res)
      | _ -> raise Not_found
    with
      Not_found ->
        let n = !i in incr i; res := (o, n) :: !res; OTInt n
  in
  let create o =
    let n = !i in incr i; res := (o, n) :: !res; OTInt n
  in
  let rec fn pos k =
    match repr k with
    | KFunc(a,b) -> kfunc (fn (neg pos) a) (fn pos b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KFixM(OConv,f) when !contract_mu && is_mu f ->
       let aux x =
         match full_repr (subst f x) with
         | KFixM(OConv,g) -> subst g x
         | _              -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = KFixM(OConv, f) in
       fn pos a'
    | KFixN(OConv,f) when !contract_mu && is_nu f ->
       let aux x =
         match full_repr (subst f x) with
         | KFixN(OConv,g) -> subst g x
         | _              -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = KFixN(OConv, f) in
       fn pos a'
    | KFixM(OVari o,f) ->
       kfixm (binder_name f) (box_of_var o) (fun x -> fn pos (subst f (KVari x)))
    | KFixN(OVari o,f) ->
       kfixn (binder_name f) (box_of_var o) (fun x -> fn pos (subst f (KVari x)))
    | KFixM(o,f) ->
       let o =
         if o <> OConv && pos <> Eps then search o
         else if o = OConv && pos = Neg then (
	   if fix then
	     let o' = OUVar(None, ref None) in create o'
	   else o)
         else o
       in
       kfixm (binder_name f) (box o) (fun x -> fn pos (subst f (KVari x)))
    | KFixN(o,f) ->
       let o =
         if o <> OConv && pos <> Eps then search o
         else if o = OConv && pos = Pos then  (
	   if fix then
	     let o' = OUVar(None, ref None) in create o'
	   else o)
         else o
       in
       kfixn (binder_name f) (box o) (fun x -> fn pos (subst f (KVari x)))
    | KDefi(d,a) -> fn pos (msubst d.tdef_value a)
    | KDPrj(t,s) -> kdprj (map_term (fn Eps) t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn pos t) s (fn Eps a)
    | KVari(x)   -> box_of_var x
    | t          -> box t
  in
  let k1 = unbox (fn (neg pos) k1) in
  let k2 = unbox (fn pos k2) in
  (k1, k2, List.rev_map (fun (a,b) -> (b,a)) !res)

let recompose : kind -> (int * ordinal) list -> kind = fun k os ->
  let get i =
    try List.assoc i os with Not_found -> assert false
  in
  let rec fn k =
    match repr k with
    | KFunc(a,b) -> kfunc (fn a) (fn b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
    | KFixM(OVari x,f) -> kfixm (binder_name f) (box_of_var x) (fun x -> fn (subst f (KVari x)))
    | KFixN(OVari x,f) -> kfixn (binder_name f) (box_of_var x) (fun x -> fn (subst f (KVari x)))
    | KFixM(OTInt i,f) -> kfixm (binder_name f) (box (get i))  (fun x -> fn (subst f (KVari x)))
    | KFixN(OTInt i,f) -> kfixn (binder_name f) (box (get i))  (fun x -> fn (subst f (KVari x)))
    | KFixM(o, f) -> kfixm (binder_name f) (box o) (fun x -> fn (subst f (KVari x)))
    | KFixN(o, f) -> kfixn (binder_name f) (box o) (fun x -> fn (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KDefi(d,a) -> fn (msubst d.tdef_value a)
    | KDPrj(t,s) -> kdprj (map_term fn t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
    | t          -> box t
  in
  unbox (fn k)
