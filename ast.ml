open Bindlib

exception Stopped

let handle_stop : bool -> unit =
  let open Sys in function
  | true  -> set_signal sigint (Signal_handle (fun i -> raise Stopped))
  | false -> set_signal sigint Signal_default

let map_opt : ('a -> 'b) -> 'a option -> 'b option = fun f o ->
  match o with
  | None   -> None
  | Some e -> Some (f e)

let from_opt : 'a option -> 'a -> 'a = fun o d ->
  match o with
  | None   -> d
  | Some e -> e

let eq_assoc : ('b -> 'b -> bool) -> ('a * 'b) list ->
               ('a * 'b) list -> bool = fun eq l1 l2 ->
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

    let in_file fname =
      let loc =
        { pos_fname = fname
        ; pos_lnum  = 1
        ; pos_bol   = 0
        ; pos_cnum  = -1 }
      in
      { loc_start = loc; loc_end = loc; loc_ghost = true }

    let none = in_file "_none_"

    let locate str pos str' pos' =
      let s = Input.lexing_position str pos in
      let e = Input.lexing_position str' pos' in
      { loc_start = s ; loc_end = e ; loc_ghost = false }
end

type pos = Location.t

type 'a position = { elt : 'a ; pos : pos }

let in_pos : pos -> 'a -> 'a position =
  fun p e -> { elt = e; pos = p }

let dummy_position : pos = Location.none

let dummy_pos : 'a -> 'a position = fun e -> in_pos dummy_position e

type strpos = string position

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
  (* Product (record) type: {l1 : A1 ; ... ; ln : An}. *)
  | Prod of (string * kind) list
  (* Sum (variant) type: [C1 of A1 | ... | Cn of An]. *)
  | DSum of (string * kind) list
  (* Quantifiers over a type: ∀/∃X A. *)
  | KAll of (kind, kind) binder
  | KExi of (kind, kind) binder
  (* Quantifiers over an ordinal: ∀/∃o A. *)
  | OAll of (ordinal, kind) binder
  | OExi of (ordinal, kind) binder
  (* Least and greatest fixpoint: μα X A, να X A. *)
  | FixM of ordinal * (kind, kind) binder
  | FixN of ordinal * (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | TDef of type_def * kind array
  (* Dot projection t.X. *)
  | DPrj of term * string
  (* With clause A with X = B. *)
  | With of kind * (string * kind)
  (**** Special constructors (not accessible to user) ****)
  (* Constants (a.k.a. epsilon) - used for subtyping. *)
  | UCst of term * (kind, kind) binder
  | ECst of term * (kind, kind) binder
  (* Unification variables - used for typechecking. *)
  | UVar of uvar
  (* Integer tag for comparing kinds. *)
  | TInt of int

and ordinal =
  (* Ordinal large enough to ensure convergence of all fixpoint. *)
  | OConv
  (* Unification variables for ordinals. *)
  | OUVar of ordinal * ordinal option ref
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
  | YNotIn of term * kind

(* Occurence markers for variables. *)
and occur =
  | Non   (* Do not occur. *)
  | Pos   (* Occurs positively only. *)
  | Neg   (* Occurs negatively only. *)
  | Both  (* Occurs both positively and negatively. *)
  | InEps (* Occurs under epsilon (special case). *)
  | Register of int * occur array * int array (* for variance in defs *)

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
  ; uvar_val : kind option ref }

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
  (* Variant. *)
  | Cons of string * term
  (* Case analysis. *)
  | Case of term * (string * term) list
  (* User-defined term. *)
  | VDef of value_def
  (* Print a string (side effect) and behave like the term. *)
  | Prnt of string
  (* Fixpoint combinator. *)
  | FixY of kind option * (term,term) binder
  (* Lambda on a type, semantics via epsilon *)
  | KAbs of (kind, term) binder
  (* Lambda on an ordinal, semantics via epsilon *)
  | OAbs of (ordinal, term) binder
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | Cnst of ((term, term) binder * kind * kind)
  (* Specific witness for recursive definitions. *)
  | CstY of ((term, term) binder * kind)
  (* Integer tag. *)
  | TagI of int

and value_def =
  (* Name of the value. *)
  { name       : string
  ; tex_name   : string
  (* The corresponding term. *)
  ; value      : term  (* evaluated *)
  ; orig_value : term (* original definition *)
  (* Raw version of the term (i.e. no anotations). *)
  ; ttype      : kind
  ; proof      : typ_proof
  ; calls      : ((int * int) list * Sct.calls) list }

and srule_name = NInd of int | NUseInd of int | NRefl | NArrow | NSum | NProd
  | NAllLeft | NAllRight | NExistsLeft | NExistsRight | NMuLeft | NMuLeftInf
  | NMuRightInf | NNuLeftInf | NNuRight | NNuRightInf | NUnknown | NProjLeft
  | NProjRight | NWithRight | NWithLeft

and sub_proof =
  { sterm             : term
  ; left              : kind
  ; right             : kind
  ; mutable unused    : ordinal list
  ; mutable strees    : sub_proof list
  ; mutable rule_name : srule_name }

and typ_proof =
  { tterm          : term
  ; typ            : kind
  ; mutable strees : sub_proof list
  ; mutable ttrees : typ_proof list }

(* Unfolding unification variable indirections. *)
let rec repr : kind -> kind = function
  | UVar({uvar_val = {contents = Some k}}) -> repr k
  | k                                      -> k

(* Unfolding unification variable indirections and definitions *)
let rec full_repr : kind -> kind = function
  | UVar({uvar_val = {contents = Some k}}) -> full_repr k
  | TDef({tdef_value = v}, a)              -> full_repr (msubst v a)
  | k                                      -> k

let rec orepr = function
  | OUVar(_, {contents = Some o}) -> orepr o
  | o                             -> o

let set v k =
  assert (!(v.uvar_val) = None);
  Timed.(v.uvar_val := Some k)

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

(* Ordinal variable management. *)
let mk_free_ovar : ovar -> ordinal =
  fun o -> OVari(o)

let new_ovar : string -> ovar =
  new_var mk_free_ovar

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

let dsum : (string * kbox) list -> kbox =
  fun cs ->
    let cs = List.map (fun (c,t) -> box_pair (box c) t) cs in
    box_apply (fun cs -> DSum(cs)) (box_list cs)

let kall : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KAll(b)) (vbind mk_free_tvar x f)

let kexi : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> KExi(b)) (vbind mk_free_tvar x f)

let oall : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> OAll(b)) (vbind mk_free_ovar x f)

let oexi : string -> (ovar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> OExi(b)) (vbind mk_free_ovar x f)

let dprj : tbox -> string -> kbox =
  fun t s ->
    box_apply (fun t -> DPrj(t,s)) t

let wIth : kbox -> string -> kbox -> kbox =
  fun a s b ->
    box_apply2 (fun a b -> With(a,(s,b))) a b

let tdef : type_def -> kbox array -> kbox =
  fun td ks -> box_apply2 (fun td ks -> TDef(td,ks)) (box td) (box_array ks)

let fixn : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_tvar x f in
    box_apply2 (fun o b -> FixN(o,b)) o b

let fixm : string -> obox -> (kvar -> kbox) -> kbox =
  fun x o f ->
    let b = vbind mk_free_tvar x f in
    box_apply2 (fun o b -> FixM(o,b)) o b

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = UVar {uvar_key = (incr c; !c); uvar_val = ref None} in
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
  unbox (kall "X" (fun x -> box_of_var x))

let top : kind =
  unbox (kexi "X" (fun x -> box_of_var x))

(****************************************************************************
 *              Functional constructors with position for terms             *
 ****************************************************************************)

let coer_p : pos -> term -> kind -> term =
  fun p t k -> in_pos p (Coer(t,k))

let lvar_p : pos -> term variable -> term =
  fun p x -> in_pos p (LVar(x))

let labs_p : pos -> kind option -> (term, term) binder -> term =
  fun p ko b -> in_pos p (LAbs(ko,b))

let kabs_p : pos -> (kind, term) binder -> term =
  fun p b -> in_pos p (KAbs b)

let oabs_p : pos -> (ordinal, term) binder -> term =
  fun p b -> in_pos p (OAbs b)

let appl_p : pos -> term -> term -> term =
  fun p t u -> in_pos p (Appl(t,u))

let reco_p : pos -> (string * term) list -> term =
  fun p fs -> in_pos p (Reco(fs))

let proj_p : pos -> term -> string -> term =
  fun p t l -> in_pos p (Proj(t,l))

let cons_p : pos -> string -> term -> term =
  fun p c t -> in_pos p (Cons(c,t))

let case_p : pos -> term -> (string * term) list -> term =
  fun p t cs -> in_pos p (Case(t,cs))

let vdef_p : pos -> value_def -> term =
  fun p v -> in_pos p (VDef(v))

let prnt_p : pos -> string -> term =
  fun p s -> in_pos p (Prnt(s))

let fixy_p : pos -> kind option -> (term, term) binder -> term =
  fun p ko t -> in_pos p (FixY(ko,t))

let cnst_p : pos -> ((term, term) binder * kind * kind) -> term =
  fun p c -> in_pos p (Cnst(c))

(****************************************************************************
 *                     Smart constructors for terms                         *
 ****************************************************************************)

let coer : pos -> tbox -> kbox -> tbox =
  fun p -> box_apply2 (coer_p p)

let lvar : pos -> term variable -> tbox =
  fun p x -> box_of_var x

let labs : pos -> kbox option -> strpos -> (tvar -> tbox) -> tbox =
  fun p ko x f ->
    box_apply2 (labs_p p) (box_opt ko) (vbind (lvar_p x.pos) x.elt f)

let kabs : pos -> strpos -> (kvar -> tbox) -> tbox =
  fun p x f ->
    box_apply (kabs_p p) (vbind mk_free_tvar x.elt f)

let oabs : pos -> strpos -> (ovar -> tbox) -> tbox =
  fun p o f ->
    box_apply (oabs_p p) (vbind mk_free_ovar o.elt f)

let idt : tbox =
  labs dummy_position None (dummy_pos "x") (fun x -> box_of_var x)

let appl : pos -> tbox -> tbox -> tbox =
  fun p -> box_apply2 (appl_p p)

let reco : pos -> (string * tbox) list -> tbox =
  fun p fs ->
    let fs = List.map (fun (l,t) -> box_pair (box l) t) fs in
    box_apply (fun fs -> reco_p p fs) (box_list fs)

let proj : pos -> tbox -> string -> tbox =
  fun p t l -> box_apply (fun t -> proj_p p t l) t

let case : pos -> tbox -> (string * tbox) list -> tbox =
  fun p t cs ->
    let aux (c,t) = box_apply (fun t -> (c,t)) t in
    box_apply2 (case_p p) t (box_list (List.map aux cs))

let cons : pos -> string -> tbox -> tbox =
  fun p c t -> box_apply (fun t -> cons_p p c t) t

let vdef : pos -> value_def -> tbox =
  fun p vd -> box (vdef_p p vd)

let prnt : pos -> string -> tbox =
  fun p s -> box (prnt_p p s)

let fixy : pos -> kbox option -> strpos -> (tvar -> tbox) -> tbox =
  fun p ko x f -> box_apply2 (fixy_p p) (box_opt ko)
                    (vbind (lvar_p x.pos) x.elt f)

(* Build a constant. Useful during typing. *)
let cnst : (term, term) binder -> kind -> kind -> term =
  fun s a b -> dummy_pos (Cnst(s,a,b))

let generic_cnst : kind -> kind -> term =
  fun a b ->
    let f = bind (lvar_p dummy_position) "x" (fun x -> x) in
    dummy_pos (Cnst(unbox f,a,b))

(****************************************************************************
 *                  Equality of types, terms and ordinals                   *
 ****************************************************************************)

let rec eq_kind : int ref -> kind -> kind -> bool = fun c k1 k2 ->
  let rec eq_kind k1 k2 = k1 == k2 ||
    match (full_repr k1, full_repr k2) with
    | (TVar(x1)   , TVar(x2)   ) -> eq_variables x1 x2
    | (Func(a1,b1), Func(a2,b2)) -> eq_kind a1 a2 && eq_kind b1 b2
    | (Prod(fs1)  , Prod(fs2)  ) -> eq_assoc eq_kind fs1 fs2
    | (DSum(cs1)  , DSum(cs2)  ) -> eq_assoc eq_kind cs1 cs2
    | (KAll(b1)   , KAll(b2)   )
    | (KExi(b1)   , KExi(b2)   ) -> eq_kbinder c b1 b2
    | (OAll(b1)   , OAll(b2)   )
    | (OExi(b1)   , OExi(b2)   ) -> eq_obinder c b1 b2
    | (FixM(o1,f1), FixM(o2,f2))
    | (FixN(o1,f1), FixN(o2,f2)) -> eq_ordinal c o1 o2 && eq_kbinder c f1 f2
    | (DPrj(t1,s1), DPrj(t2,s2)) -> s1 = s2 && eq_term c t1 t2
    | (With(a1,e1), With(a2,e2)) -> let (s1,b1) = e1 and (s2,b2) = e2 in
                                    eq_kind a1 a2 && s1 = s2 && eq_kind b1 b2
    | (UCst(t1,f1), UCst(t2,f2))
    | (ECst(t1,f1), ECst(t2,f2)) -> eq_kbinder c f1 f2 && eq_term c t1 t2
    | (UVar(u1)   , UVar(u2)   ) -> u1.uvar_key = u2.uvar_key
    | (TInt(i1)   , TInt(i2)   ) -> i1 = i2
    | (_          , _          ) -> false
  in
  eq_kind k1 k2

and eq_kbinder c f1 f2 = f1 == f2 ||
  let i = incr c; TInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_obinder c f1 f2 = f1 == f2 ||
  let i = incr c; OTInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_tbinder c f1 f2 = f1 == f2 ||
  let i = incr c; dummy_pos (TagI(!c)) in
  eq_term c (subst f1 i) (subst f2 i)

and eq_term : int ref -> term -> term -> bool = fun c t1 t2 ->
  let rec eq_term t1 t2 =
    t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (Coer(t1,_) , _          ) -> eq_term t1 t2
    | (_          , Coer(t2,_) ) -> eq_term t1 t2
    | (VDef(d1)   , _          ) -> eq_term d1.value t2
    | (_          , VDef(d2)   ) -> eq_term t1 d2.value
    | (KAbs(f)    , _          ) -> eq_term (subst f (Prod[])) t2
    | (_          , KAbs(f)    ) -> eq_term t1 (subst f (Prod[]))
    | (OAbs(f)    , _          ) -> eq_term (subst f (OTInt(-1))) t2
    | (_          , OAbs(f)    ) -> eq_term t1 (subst f (OTInt(-1)))
    | (LVar(x1)   , LVar(x2)   ) -> eq_variables x1 x2
    | (LAbs(_,f1) , LAbs(_,f2) )
    | (FixY(_,f1) , FixY(_,f2) ) -> eq_tbinder c f1 f2
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_term t1 t2 && eq_term u1 u2
    | (Reco(fs1)  , Reco(fs2)  ) -> eq_assoc eq_term fs1 fs2
    | (Proj(t1,l1), Proj(t2,l2)) -> l1 = l2 && eq_term t1 t2
    | (Cons(c1,t1), Cons(c2,t2)) -> c1 = c2 && eq_term t1 t2
    | (Case(t1,l1), Case(t2,l2)) -> eq_term t1 t2 && eq_assoc eq_term l1 l2
    | (Prnt(s1)   , Prnt(s2)   ) -> s1 = s2
    | (Cnst(c1)   , Cnst(c2)   ) -> let (f1,a1,b1) = c1 and (f2,a2,b2) = c2 in
                                    eq_tbinder c f1 f2 && eq_kind c a1 a2
                                    && eq_kind c b1 b2
    | (CstY(f1,a1), CstY(f2,a2)) -> eq_tbinder c f1 f2 && eq_kind c a1 a2
    | (_          , _          ) -> false
  in eq_term t1 t2

and eq_ordinal : int ref -> ordinal -> ordinal -> bool = fun c o1 o2 ->
  match (orepr o1, orepr o2) with
  | (o1          , o2          ) when o1 == o2 -> true
  | (OConv       , OConv       ) -> true
  | (OUVar(o',p) , o           )
  | (o           , OUVar(o',p) ) -> Timed.pure_test (less_ordinal c o) o' &&
                                    (assert(!p = None); Timed.(p := Some o); true)
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
  | (YNotIn(t1,k1), YNotIn(t2,k2)) -> eq_term c t1 t2 && eq_kind c k1 k2
  | (_            , _            ) -> false

and leq_ordinal c o1 o2 =
  match (orepr o1, orepr o2) with
  | (o1         , o2        ) when o1 == o2 -> true
  | (_          , OConv     ) -> true
  | (OUVar(o, p), o2        ) -> Timed.pure_test (leq_ordinal c o) o2 || (
                                   Timed.pure_test (less_ordinal c o2) o &&
                                   (assert(!p = None); Timed.(p := Some o2); true))
  | (o1         , OUVar(o,p)) -> Timed.pure_test (less_ordinal c o1) o &&
                                 (assert(!p = None); Timed.(p := Some o1); true)
  | (OLess(o1,_), o2        ) -> leq_ordinal c o1 o2
  | (OMaxi(l1)  , o2        ) -> List.for_all (fun o1 -> leq_ordinal c o1 o2) l1
  | (o1         , OMaxi(l2) ) -> List.exists (fun o2 -> leq_ordinal c o1 o2) l2
  | (_          , _         ) -> false

and less_ordinal c o1 o2 =
  let o1 = orepr o1 and o2 = orepr o2 in
  match o1 with
  | OLess(o,_) -> leq_ordinal c o o2
  | OUVar(o,_) -> less_ordinal c o o2
  | OMaxi(l1)  -> List.for_all (fun o1 -> less_ordinal c o1 o2) l1
  | _          -> false

(* FIXME: normalize elements, sort, eliminate duplicate, hashcons ? *)
let omax = function
  | []  -> assert false
  | [o] -> o
  | l   -> Printf.eprintf "USE MAX\n%!"; OMaxi l

let eq_kind : kind -> kind -> bool =
  fun k1 k2 -> eq_kind (ref 0) k1 k2

let eq_term : term -> term -> bool =
  fun t1 t2 -> eq_term (ref 0) t1 t2

let eq_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> eq_ordinal (ref 0) t1 t2

let eq_ord_wit : ord_wit -> ord_wit -> bool =
  fun t1 t2 -> eq_ord_wit (ref 0) t1 t2

let leq_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> leq_ordinal (ref 0) t1 t2

let less_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> less_ordinal (ref 0) t1 t2

let eq_head_term t u =
  let rec fn u =
    t == u || eq_term t u ||
    match u.elt with
    | Appl(u,_)
    | Case(u,_)
    | Proj(u,_) -> fn u
    | KAbs(f)   -> fn (subst f (Prod[]))
    | OAbs(f)   -> fn (subst f (OTInt(-1)))
    | _         -> false
  in fn u

 (***************************************************************************
 *                             mapping on terms                             *
 ****************************************************************************)

let map_term : (kind -> kbox) -> term -> tbox = fun kn t ->
  let rec fn t =
    match t.elt with
    | Coer(t,k)  -> coer t.pos (fn t) (kn k)
    | LVar x     -> box_of_var x
    | LAbs(ko,f) -> let ko = map_opt kn ko in
                    labs t.pos ko (in_pos t.pos (binder_name f))
                      (fun x -> fn (subst f (dummy_pos (LVar x))))
    | FixY(ko,f) -> let ko = map_opt kn ko in
                    fixy t.pos ko (in_pos t.pos (binder_name f))
                      (fun x -> fn (subst f (dummy_pos (LVar x))))
    | KAbs(f)    -> kabs t.pos (dummy_pos (binder_name f))
                      (fun x -> fn (subst f (TVar x)))
    | OAbs(f)    -> oabs t.pos (dummy_pos (binder_name f))
                      (fun x -> fn (subst f (OVari x)))
    | Appl(a,b)  -> appl t.pos (fn a) (fn b)
    | Reco(fs)   -> reco t.pos (List.map (fun (s,a) -> (s, fn a)) fs)
    | Proj(a,s)  -> proj t.pos (fn a) s
    | Cons(s,a)  -> cons t.pos s (fn a)
    | Case(a,fs) -> case t.pos (fn a) (List.map (fun (s,a) -> (s, fn a)) fs)
    | u          -> box_apply (in_pos t.pos) (box u)
  in fn t

(****************************************************************************
 *                 Occurence test for unification variables                 *
 ****************************************************************************)

let combine oa ob =
  match (oa, ob) with
  | (Register _,          _) -> assert false
  | (_         , Register _) -> assert false
  | (Non       , _         ) -> ob
  | (_         , Non       ) -> oa
  | (InEps     , _         ) -> InEps
  | (_         , InEps     ) -> InEps
  | (Both      , _         ) -> Both
  | (_         , Both      ) -> Both
  | (Neg       , Pos       ) -> Both
  | (Pos       , Neg       ) -> Both
  | (Neg       , Neg       ) -> Neg
  | (Pos       , Pos       ) -> Pos

let compose oa ob =
  match (oa, ob) with
  | (Register _, _         ) -> assert false
  | (_         , Register _) -> assert false
  | (Non       , _         ) -> Non
  | (_         , Non       ) -> Non
  | (InEps     , _         ) -> InEps
  | (_         , InEps     ) -> InEps
  | (Both      , _         ) -> Both
  | (_         , Both      ) -> Both
  | (Neg       , Pos       ) -> Neg
  | (Pos       , Neg       ) -> Neg
  | (Neg       , Neg       ) -> Pos
  | (Pos       , Pos       ) -> Pos

let compose2 (oa,da) (ob,db) =
  let o =
    match (oa, ob) with
    | (Register(i,a,d), p) -> a.(i) <- combine a.(i) p;
                              d.(i) <- min d.(i) (db - da); Non
    | _                    -> compose oa ob
  in (o, da + db)

let neg = function
  | Register _ -> assert false
  | Neg        -> Pos
  | Pos        -> Neg
  | o          -> o

(* FIXME: should memoize this function, because a lot of sub-term are shared
   and we traverse all constants ... One could also precompute the
   variance of definitions to avoid substitution *)
let uvar_occur : uvar -> kind -> occur = fun {uvar_key = i} k ->
  let dummy = Prod [] in
  let odummy = OTInt(-42) in
  let rec aux occ acc k =
    match repr k with
    | TVar(x)   -> acc
    | Func(a,b) -> aux (neg occ) (aux occ acc b) a
    | Prod(ks)
    | DSum(ks)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc ks
    | KAll(f)
    | KExi(f)   -> aux occ acc (subst f dummy)
    | OAll(f)
    | OExi(f)   -> aux occ acc (subst f odummy)
    | FixM(o,f)
    | FixN(o,f) -> aux occ (aux3 acc o) (subst f dummy)
    | DPrj(t,_) -> aux2 acc t
    | With(a,_) -> aux occ acc a (* FIXME *)
    | TDef(d,a) ->
       let acc = ref acc in
       Array.iteri (fun i k ->
         acc := aux (compose occ d.tdef_variance.(i)) !acc k) a;
       !acc
    | UCst(t,f)
    | ECst(t,f) -> let a = subst f dummy in aux2 (aux InEps acc a) t
    | UVar(u)   -> if u.uvar_key = i then combine acc occ else acc
    | TInt(_)   -> assert false
  and aux2 acc t = match t.elt with
    | Cnst(t,k1,k2) -> aux2 (aux InEps (aux InEps acc k1) k2) (subst t (dummy_pos (Reco [])))
    | CstY(t,k)     -> aux2 (aux InEps acc k) (subst t (dummy_pos (Reco [])))
    | Coer(t,_)
    | Proj(t,_)
    | Cons(_,t)     -> aux2 acc t
    | FixY(_,f)
    | LAbs(_,f)     -> aux2 acc (subst f (dummy_pos (Reco [])))
    | KAbs(f)       -> aux2 acc (subst f (Prod []))
    | OAbs(f)       -> aux2 acc (subst f (OTInt(-1)))
    | Appl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | Reco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | Case(t,l)     -> List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | LVar _
    | VDef _
    | Prnt _
    | TagI _        -> acc
  and aux3 acc = function
    | OLess(o,(In(t,f)|NotIn(t,f))) -> aux InEps (aux2 (aux3 acc o) t) (subst f odummy)
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
      | Func(a,b) -> func (fn a) (fn b)
      | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn a)) fs)
      | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KAll(f)   -> kall (binder_name f) (fun x -> fn (subst f (TVar x)))
      | KExi(f)   -> kexi (binder_name f) (fun x -> fn (subst f (TVar x)))
      | OAll(f)   -> oall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | OExi(f)   -> oexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | FixM(o,f) -> fixm (binder_name f) (gn o) (fun x -> fn (subst f (TVar x)))
      | FixN(o,f) -> fixn (binder_name f) (gn o) (fun x -> fn (subst f (TVar x)))
      | TVar x    -> box_of_var x
      | TDef(d,a) -> tdef d (Array.map fn a)
      | DPrj(t,s) -> dprj (map_term fn t) s
      | With(t,(s,a)) -> wIth (fn t) s (fn a)
      | t         -> box t
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
  unbox (bind mk_free_tvar "X" (fun x ->
    let rec fn k =
      match repr k with
      | Func(a,b) -> func (fn a) (fn b)
      | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn a)) fs)
      | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KAll(f)   -> kall (binder_name f) (fun x -> fn (subst f (TVar x)))
      | KExi(f)   -> kexi (binder_name f) (fun x -> fn (subst f (TVar x)))
      | OAll(f)   -> oall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | OExi(f)   -> oexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | FixM(o,f) -> fixm (binder_name f) (gn o) (fun x -> fn (subst f (TVar x)))
      | FixN(o,f) -> fixn (binder_name f) (gn o) (fun x -> fn (subst f (TVar x)))
      | UVar(u)   -> assert(!(u.uvar_val) = None); if u.uvar_key = i then x else box k
      | TVar x    -> box_of_var x
      | TDef(d,a) -> tdef d (Array.map fn a)
      | DPrj(t,s) -> dprj (map_term fn t) s
      | With(t,(s,a)) -> wIth (fn t) s (fn a)
      | t         -> box t
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | o -> box o
    in
    fn k))

(****************************************************************************
 *                    Decomposition type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

let contract_mu = ref true
let is_mu f = !contract_mu &&
  match full_repr (subst f (Prod [])) with FixM(OConv,_) -> true
  | _ -> false
let is_nu f = !contract_mu &&
  match full_repr (subst f (Prod [])) with FixN(OConv,_) -> true
  | _ -> false

let decompose : ord_wit option -> occur -> kind -> kind -> kind * kind * (int * ordinal) list = fun fix pos k1 k2 ->
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
    | Func(a,b) -> func (fn (neg pos) a) (fn pos b)
    | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | KAll(f)   -> kall (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | KExi(f)   -> kexi (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | OAll(f)   -> oall (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | OExi(f)   -> oexi (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | FixM(OConv,f) when !contract_mu && is_mu f ->
       let aux x =
         match full_repr (subst f x) with
         | FixM(OConv,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = FixM(OConv, f) in
       fn pos a'
    | FixN(OConv,f) when !contract_mu && is_nu f ->
       let aux x =
         match full_repr (subst f x) with
         | FixN(OConv,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = FixN(OConv, f) in
       fn pos a'
    | FixM(OVari o,f) ->
       fixm (binder_name f) (box_of_var o)
         (fun x -> fn pos (subst f (TVar x)))
    | FixN(OVari o,f) ->
       fixn (binder_name f) (box_of_var o)
         (fun x -> fn pos (subst f (TVar x)))
    | FixM(o,f) ->
       let o =
         if o <> OConv && pos <> InEps then search o
         else if o = OConv && pos = Neg then (match fix with
           None -> o
         | Some w ->
            let o' = OLess(o,w) in create o')
         else o
       in
       fixm (binder_name f) (box o) (fun x -> fn pos (subst f (TVar x)))
    | FixN(o,f) ->
       let o =
         if o <> OConv && pos <> InEps then search o
         else if o = OConv && pos = Pos then (match fix with
           None -> o
         | Some w ->
            let o' = OLess(o,w) in create o')
         else o
       in
       fixn (binder_name f) (box o) (fun x -> fn pos (subst f (TVar x)))
    | TDef(d,a) -> fn pos (msubst d.tdef_value a)
    | DPrj(t,s) -> dprj (map_term (fn InEps) t) s
    | With(t,(s,a)) -> wIth (fn pos t) s (fn InEps a)
    | TVar x    -> box_of_var x
    | t         -> box t
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
    | Func(a,b) -> func (fn a) (fn b)
    | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn a)) fs)
    | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn a)) cs)
    | KAll(f)   -> kall (binder_name f) (fun x -> fn (subst f (TVar x)))
    | KExi(f)   -> kexi (binder_name f) (fun x -> fn (subst f (TVar x)))
    | OAll(f)   -> oall (binder_name f) (fun x -> fn (subst f (OVari x)))
    | OExi(f)   -> oexi (binder_name f) (fun x -> fn (subst f (OVari x)))
    | FixM(OVari x,f) -> fixm (binder_name f) (box_of_var x) (fun x -> fn (subst f (TVar x)))
    | FixN(OVari x,f) -> fixn (binder_name f) (box_of_var x) (fun x -> fn (subst f (TVar x)))
    | FixM(OTInt i,f) -> fixm (binder_name f) (box (get i))  (fun x -> fn (subst f (TVar x)))
    | FixN(OTInt i,f) -> fixn (binder_name f) (box (get i))  (fun x -> fn (subst f (TVar x)))
    | FixM(o, f) -> fixm (binder_name f) (box o) (fun x -> fn (subst f (TVar x)))
    | FixN(o, f) -> fixn (binder_name f) (box o) (fun x -> fn (subst f (TVar x)))
    | TVar x    -> box_of_var x
    | TDef(d,a) -> fn (msubst d.tdef_value a)
    | DPrj(t,s) -> dprj (map_term fn t) s
    | With(t,(s,a)) -> wIth (fn t) s (fn a)
    | t         -> box t
  in
  unbox (fn k)
