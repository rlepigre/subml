open Bindlib
open Util

(****************************************************************************
 *                                 Ordinals                                 *
 ****************************************************************************)

type ordinal =
  | ODumm
  | OConv
  | OLess of int * ordinal
  | OLEqu of int * ordinal

let rec leq_ordinal o1 o2 =
  match (o1, o2) with
  | (ODumm       , _           ) -> false
  | (_           , ODumm       ) -> false
  | (OLess(n1,_ ), OLess(n2,_ )) when n1 = n2 -> true
  | (OLEqu(n1,_ ), OLEqu(n2,_ )) when n1 = n2 -> true
  | (OLess(n1,o1), OLess(n2,_ )) when n1 > n2 -> leq_ordinal o1 o2
  | (OLess(n1,o1), OLEqu(n2,_ )) when n1 > n2 -> leq_ordinal o1 o2
  | (OLEqu(n1,o1), OLess(n2,_ )) when n1 > n2 -> leq_ordinal o1 o2
  | (OLEqu(n1,o1), OLEqu(n2,_ )) when n1 > n2 -> leq_ordinal o1 o2
  | (_           , OConv       ) -> true
  | (_           , _           ) -> false

let rec less_ordinal o1 o2 =
  match o1 with
  | OLess(n1,o1) -> leq_ordinal o1 o2
  | OLEqu(n1,o1) -> less_ordinal o1 o2
  | _            -> false

let new_oless, new_olequ, oreset =
  let e = ref 0 in
  let new_oless o = incr e; OLess(!e, o) in
  let new_olequ o = incr e; OLEqu(!e, o) in
  let oreset () = e := 0 in
  (new_oless, new_olequ, oreset)

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
  (* Quantifiers: ∀/∃X A. *)
  | FAll of (kind, kind) binder
  | Exis of (kind, kind) binder
  (* Least and greatest fixpoint: μα X A, να X A. *)
  | FixM of ordinal * (kind, kind) binder
  | FixN of ordinal * (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | TDef of type_def * kind array
  (**** Special constructors (not accessible to user) ****)
  (* Constants (a.k.a. epsilon) - used for subtyping. *)
  | UCst of qcst
  | ECst of qcst
  (* Unification variables - used for typechecking. *)
  | UVar of uvar
  (* Integer tag for comparing kinds. *)
  | TInt of int

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

(* Quantifier constant. *)
and qcst =
  { qcst_key      : int (* NOTE Not sure if useful. *)
  ; qcst_wit_term : term
  ; qcst_wit_kind : (kind, kind) binder }

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
  (* Variant. *)
  | Cons of string * term
  (* Case analysis. *)
  | Case of term * (string * (term, term) binder) list
  (* User-defined term. *)
  | VDef of value_def
  (* Print a string (side effect) and behave like the term. *)
  | Prnt of string * term
  (* Fixpoint combinator. *)
  | FixY
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | Cnst of ((term, term) binder * kind * kind)
  (* Integer tag. *)
  | TagI of int
  
and value_def =
  (* Name of the value. *)
  { name  : string
  (* The corresponding term. *)
  ; value : term
  (* Raw version of the term (i.e. no anotations). *)
  ; ttype : kind option }

(****************************************************************************
 *                        Equality of types and terms                       *
 ****************************************************************************)

let rec eq_kind : int ref -> kind -> kind -> bool = fun c k1 k2 ->
  let rec eq_kind k1 k2 = k1 == k2 ||
    match (k1,k2) with
    | (TVar(x1)   , TVar(x2)   ) -> eq_variables x1 x2
    | (Func(a1,b1), Func(a2,b2)) -> eq_kind a1 a2 && eq_kind b1 b2
    | (Prod(fs1)  , Prod(fs2)  ) -> eq_assoc eq_kind fs1 fs2
    | (DSum(cs1)  , DSum(cs2)  ) -> eq_assoc eq_kind cs1 cs2
    | (FAll(b1)   , FAll(b2)   ) -> eq_kbinder b1 b2
    | (Exis(b1)   , Exis(b2)   ) -> eq_kbinder b1 b2
    | (FixM(o1,f1), FixM(o2,f2)) -> o1 = o2 && eq_kbinder f1 f2
    | (FixN(o1,f1), FixN(o2,f2)) -> o1 = o2 && eq_kbinder f1 f2
    | (TDef(d1,a1), TDef(d2,a2)) ->
        let k1 = msubst d1.tdef_value a1 in
        let k2 = msubst d2.tdef_value a2 in
        eq_kind k1 k2
    | (UCst(c1)   , UCst(c2)   ) ->
        eq_kbinder c1.qcst_wit_kind c2.qcst_wit_kind &&
        eq_term c c1.qcst_wit_term c2.qcst_wit_term
    | (ECst(c1)   , ECst(c2)   ) ->
        eq_kbinder c1.qcst_wit_kind c2.qcst_wit_kind &&
        eq_term c c1.qcst_wit_term c2.qcst_wit_term
    | (UVar(u1)   , UVar(u2)   ) -> u1.uvar_key = u2.uvar_key
    | (TInt(i1)   , TInt(i2)   ) -> i1 = i2
    | (_          , _          ) -> false
  and eq_kbinder f1 f2 = f1 == f2 ||
    let i = incr c; TInt(!c) in
    eq_kind (subst f1 i) (subst f2 i)
  in
  eq_kind k1 k2

and eq_term : int ref -> term -> term -> bool = fun c t1 t2 ->
  let rec eq_term t1 t2 = t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (Coer(t1,_) , Coer(t2,_) ) -> eq_term t1 t2
    | (LVar(x1)   , LVar(x2)   ) -> eq_variables x1 x2
    | (LAbs(_,f1) , LAbs(_,f2) ) -> eq_tbinder f1 f2
    | (Appl(t1,u1), Appl(t2,u2)) -> eq_term t1 t2 && eq_term u1 u2
    | (Reco(fs1)  , Reco(fs2)  ) -> eq_assoc eq_term fs1 fs2
    | (Proj(t1,l1), Proj(t2,l2)) -> l1 = l2 && eq_term t1 t2
    | (Cons(c1,t1), Cons(c2,t2)) -> c1 = c2 && eq_term t1 t2
    | (Case(t1,l1), Case(t2,l2)) -> eq_term t1 t2 && eq_assoc eq_tbinder l1 l2
    | (VDef(d1)   , VDef(d2)   ) -> eq_term d1.value d2.value
    | (Prnt(s1,t1), Prnt(s2,t2)) -> s1 = s2 && eq_term t1 t2
    | (FixY       , FixY       ) -> true
    | (Cnst(c1)   , Cnst(c2)   ) ->
        let (f1,a1,b1) = c1 and (f2,a2,b2) = c2 in
        eq_tbinder f1 f2 && eq_kind c a1 a2 && eq_kind c b1 b2
    | (_          , _          ) -> false
  and eq_tbinder f1 f2 =
    let a = incr c; dummy_pos (TagI(!c)) in
    eq_term (subst f1 a) (subst f2 a)
  in
  eq_term t1 t2

let eq_kind : kind -> kind -> bool = fun k1 k2 ->
  let c = ref 0 in
  eq_kind c k1 k2

let eq_term : term -> term -> bool = fun t1 t2 ->
  let c = ref 0 in
  eq_term c t1 t2

(****************************************************************************
 *                   Frequently used types and functions                    *
 ****************************************************************************)

(* Value and type environments. *)
type val_env = (string, value_def) Hashtbl.t
type typ_env = (string, type_def ) Hashtbl.t

(* State. *)
type state =
  { tenv : typ_env
  ; venv : val_env
  ; mutable verbose : bool }

let initial_state : bool -> state = fun v ->
  { tenv = Hashtbl.create 17
  ; venv = Hashtbl.create 17
  ; verbose = v }

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

(* Unfolding unification variable indirections. *)
let rec uvar_repr : uvar -> kind = fun u ->
  match u.uvar_val with
  | None           -> UVar u
  | Some (UVar u') -> uvar_repr u'
  | Some k         -> k

let repr : kind -> kind = function
  | UVar u -> uvar_repr u
  | k      -> k

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

let fall : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> FAll(b)) (bind mk_free_tvar x f)

let exis : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> Exis(b)) (bind mk_free_tvar x f)

let tdef : type_def -> kbox array -> kbox =
  fun td ks -> box_apply2 (fun td ks -> TDef(td,ks)) (box td) (box_array ks)

let fixn : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x f in
    box_apply (fun b -> FixN(OConv,b)) b

let fixm : string -> (kbox -> kbox) -> kbox =
  fun x f ->
    let b = bind mk_free_tvar x f in
    box_apply (fun b -> FixM(OConv,b)) b

(* Quantifier constant management. *)
let (new_ucst, reset_ucst) =
  let c = ref 0 in
  let new_ucst t f = UCst
    { qcst_key      = (incr c; !c)
    ; qcst_wit_term = t
    ; qcst_wit_kind = f }
  in
  let reset_ucst () = c := 0 in
  (new_ucst, reset_ucst)

let (new_ecst, reset_ecst) =
  let c = ref 0 in
  let new_ecst t f = ECst
    { qcst_key      = (incr c; !c)
    ; qcst_wit_term = t
    ; qcst_wit_kind = f }
  in
  let reset_ecst () = c := 0 in
  (new_ecst, reset_ecst)

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = UVar {uvar_key = (incr c; !c); uvar_val = None} in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(* Resset all counters. *)
let reset_all () =
  let reset = [reset_ucst; reset_ecst; reset_uvar; oreset] in
  List.iter (fun x -> x ()) reset

(****************************************************************************
 *                     Definition of widely used types                      *
 ****************************************************************************)

let fix_kind : kind =
  unbox (fall "X" (fun x -> func (func x x) x))

let bot : kind =
  unbox (fall "X" (fun x -> x))

let top : kind =
  unbox (exis "X" (fun x -> x))

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

let cons_p : pos -> string -> term -> term =
  fun p c t -> in_pos p (Cons(c,t))

let case_p : pos -> term -> (string * (term, term) binder) list -> term =
  fun p t cs -> in_pos p (Case(t,cs))

let vdef_p : pos -> value_def -> term =
  fun p v -> in_pos p (VDef(v))

let prnt_p : pos -> string -> term -> term =
  fun p s t -> in_pos p (Prnt(s,t))

let fixy_p : pos -> term =
  fun p -> in_pos p FixY

let cnst_p : pos -> ((term, term) binder * kind * kind) -> term =
  fun p c -> in_pos p (Cnst(c))
 
(****************************************************************************
 *                     Smart constructors for terms                         *
 ****************************************************************************)

let coer : pos -> tbox -> kbox -> tbox =
  fun p -> box_apply2 (coer_p p)

let lvar : pos -> term variable -> tbox =
  fun p x -> box_of_var x

let labs : pos -> kbox option -> strpos -> (tbox -> tbox) -> tbox =
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

let case : pos -> tbox -> (string * strpos * (tbox -> tbox)) list -> tbox =
  fun p t cs ->
    let aux (c,x,f) =
      let b = bind (lvar_p x.pos) x.elt f in
      box_pair (box c) b
    in
    box_apply2 (case_p p) t (box_list (List.map aux cs))

let cons : pos -> string -> tbox -> tbox =
  fun p c t -> box_apply (fun t -> cons_p p c t) t

let vdef : pos -> value_def -> tbox =
  fun p vd -> box (vdef_p p vd)

let prnt : pos -> string -> tbox -> tbox =
  fun p s -> box_apply (prnt_p p s)

let fixy : pos -> tbox =
  fun p -> box (fixy_p p)

(* Build a constant. Useful during typing. *)
let cnst : (term, term) binder -> kind -> kind -> term =
  fun s a b -> dummy_pos (Cnst(s,a,b))

let generic_cnst : kind -> kind -> term =
  fun a b ->
    let f = bind (lvar_p dummy_position) "x" (fun x -> x) in
    dummy_pos (Cnst(unbox f,a,b))

(****************************************************************************
 *                 Occurence test for unification variables                 *
 ****************************************************************************)

let uvar_occur : uvar -> kind -> occur = fun {uvar_key = i} k ->
  let combine oa ob =
    match (oa, ob) with
    | (Non  , _    ) -> ob
    | (_    , Non  ) -> oa
    | (InEps, _    ) -> InEps
    | (_    , InEps) -> InEps
    | (Both , _    ) -> Both
    | (_    , Both ) -> Both
    | (Neg  , Pos  ) -> Both
    | (Pos  , Neg  ) -> Both
    | (Neg  , Neg  ) -> Neg
    | (Pos  , Pos  ) -> Pos
  in
  let neg = function
    | Neg -> Pos
    | Pos -> Neg
    | o   -> o
  in
  let dummy = Prod [] in
  let rec aux occ acc = function
    | TVar(x)   -> acc
    | Func(a,b) -> aux (neg occ) (aux occ acc b) a
    | Prod(fs)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc fs
    | DSum(cs)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc cs
    | FAll(f)   -> aux occ acc (subst f dummy)
    | Exis(f)   -> aux occ acc (subst f dummy)
    | FixM(_,f) -> aux occ acc (subst f dummy) (* FIXME is that right ? *)
    | FixN(_,f) -> aux occ acc (subst f dummy) (* FIXME is that right ? *)
    | TDef(d,a) -> aux occ acc (msubst d.tdef_value a)
    | UCst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux InEps acc a
    | ECst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux InEps acc a
    | UVar(u)   -> if u.uvar_key = i then combine acc occ else acc
    | TInt(_)   -> assert false
  in aux Pos Non k

(****************************************************************************
 *                 Binding a unification variable in a type                 *
 ****************************************************************************)

let bind_uvar : uvar -> kind -> kind -> kind = fun {uvar_key = i} k x ->
  let rec subst k =
    match repr k with
    | TVar(_)   -> k
    | Func(a,b) -> Func(subst a, subst b)
    | Prod(fs)  -> Prod(List.map (fun (l,a) -> (l, subst a)) fs)
    | DSum(cs)  -> DSum(List.map (fun (c,a) -> (c, subst a)) cs)
    | FAll(f)   -> FAll(binder_compose_right f subst)
    | Exis(f)   -> Exis(binder_compose_right f subst)
    | FixM(o,f) -> FixM(o,binder_compose_right f subst)
    | FixN(o,f) -> FixN(o,binder_compose_right f subst)
    | TDef(d,a) -> TDef(d, Array.map subst a)
    | UCst(_)   -> assert false (* TODO *)
    | ECst(_)   -> assert false (* TODO *)
    | UVar(u)   -> if u.uvar_key = i then x else k
    | TInt(_)   -> assert false
  in
  subst k

(****************************************************************************
 *                                 Lower kind                               *
 ****************************************************************************)
let rec leq_level l1 l2 =
  match (l1, l2) with
  | (_    , []   ) -> true
  | (x::l1, y::l2) when x = y -> leq_level l1 l2
  | (_    , _    ) -> false

let lower_kind k1 k2 =
  let i = ref 0 in
  let new_int () = incr i; TInt !i in
  let rec lower_kind k1 k2 =
    match (repr k1, repr k2) with
    | (k1          , k2          ) when k1 == k2 -> true
    | (TVar(_)     , TVar(_)     ) -> assert false
    | (Func(a1,b1) , Func(a2,b2) ) -> lower_kind a2 a1 && lower_kind b1 b2
    | (Prod(fsa)   , Prod(fsb)   ) ->
        let cmp (k1,_) (k2,_) = compare k1 k2 in
        let f (la,a) (lb,b) = la = lb && lower_kind a b in
        List.for_all2 f (List.sort cmp fsa) (List.sort cmp fsb)
    | (FAll(a)     , FAll(b)     ) ->
        let i = new_int () in
        lower_kind (subst a i) (subst b i)
    | (Exis(a)     , FAll(b)     ) ->
        let i = new_int () in
        lower_kind (subst a i) (subst b i)
    | (FixM(oa,fa) , FixM(ob,fb) ) ->
        leq_ordinal oa ob && (fa == fb ||
          let i = new_int () in lower_kind (subst fa i) (subst fb i))
    | (FixN(oa,fa) , FixN(ob,fb) ) ->
        leq_ordinal ob oa && (fa == fb ||
          let i = new_int () in lower_kind (subst fa i) (subst fb i))
    | (TDef(da,aa) , TDef(db,ab) ) ->
        lower_kind (msubst da.tdef_value aa) (msubst db.tdef_value ab)
    | (UCst(ca)    , UCst(cb)    ) ->
        let i = new_int () in
        let a = subst ca.qcst_wit_kind i in
        let b = subst cb.qcst_wit_kind i in
        lower_kind a b && ca.qcst_wit_term == cb.qcst_wit_term
        (* FIXME what of the bound ? *)
    | (ECst(ca)    , ECst(cb)    ) ->
        let i = new_int () in
        let a = subst ca.qcst_wit_kind i in
        let b = subst cb.qcst_wit_kind i in
        lower_kind a b && ca.qcst_wit_term == cb.qcst_wit_term
        (* FIXME what of the bound ? *)
    | (UVar(ua)    , UVar(ub)    ) when ua == ub -> true
    | (TInt(ia)    , TInt(ib)    ) -> ia = ib
    | (_           , _           ) -> false
  in lower_kind k1 k2
