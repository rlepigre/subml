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

and ordinal =
  | OConv
  | OLess of ordinal * term * ord_constraint
  | OLEqu of ordinal * term * ord_constraint
  (* integer tag for comparing ordinals *)
  | OTag of int
  (* *)
  | ODumm

and ord_constraint =
  | In of (ordinal,kind) binder
  | NotIn of (ordinal,kind) binder

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
  ; tdef_tex_name : string
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
  | Case of term * (string * term) list
  (* User-defined term. *)
  | VDef of value_def
  (* Print a string (side effect) and behave like the term. *)
  | Prnt of string
  (* Fixpoint combinator. *)
  | FixY of term
  (**** Special constructors (not accessible to user) ****)
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | Cnst of ((term, term) binder * kind * kind)
  (* Integer tag. *)
  | TagI of int

and value_def =
  (* Name of the value. *)
  { name  : string
  ; tex_name : string
  (* The corresponding term. *)
  ; value : term
  (* Raw version of the term (i.e. no anotations). *)
  ; ttype : kind
  ; proof : typ_proof }

and sub_proof =
  { sterm : term;
    left : kind;
    right : kind;
    unused : ordinal option ref;
    mutable strees : sub_proof list }

and typ_proof =
  { tterm : term;
    typ : kind;
    mutable strees : sub_proof list;
    mutable ttrees : typ_proof list;
  }

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
    | (FixM(o1,f1), FixM(o2,f2)) -> eq_ordinal c o1 o2 && eq_kbinder f1 f2
    | (FixN(o1,f1), FixN(o2,f2)) -> eq_ordinal c o1 o2 && eq_kbinder f1 f2
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
    | (Case(t1,l1), Case(t2,l2)) -> eq_term t1 t2 && eq_assoc eq_term l1 l2
    | (VDef(d1)   , VDef(d2)   ) -> eq_term d1.value d2.value
    | (Prnt(s1)   , Prnt(s2)   ) -> s1 = s2
    | (FixY(t1)   , FixY(t2)   ) -> eq_term t1 t2
    | (Cnst(c1)   , Cnst(c2)   ) ->
        let (f1,a1,b1) = c1 and (f2,a2,b2) = c2 in
        eq_tbinder f1 f2 && eq_kind c a1 a2 && eq_kind c b1 b2
    | (_          , _          ) -> false
  and eq_tbinder f1 f2 =
    let a = incr c; dummy_pos (TagI(!c)) in
    eq_term (subst f1 a) (subst f2 a)
  in
  eq_term t1 t2

and eq_ordinal : int ref -> ordinal -> ordinal -> bool = fun c o1 o2 ->
  let rec eq_ordinal o1 o2 =
    if o1 == o2 then true else
      match o1, o2 with
      | ODumm, ODumm -> true
      | OConv, OConv -> true
      | OLEqu(o1,t1,c1), OLEqu(o2,t2,c2)
      | OLess(o1,t1,c1), OLess(o2,t2,c2) -> eq_ordinal o1 o2 && eq_term c t1 t2 && eq_ocst c1 c2
      | OTag n1, OTag n2 -> n1 = n2
      | _ -> false
  and eq_ocst c1 c2 =
    let o = incr c; OTag (!c) in
    match c1, c2 with
    | In f1, In f2
    | NotIn f1, NotIn f2 -> eq_kind c (subst f1 o) (subst f2 o)
    | _ -> false
  in eq_ordinal o1 o2

let eq_kind : kind -> kind -> bool = fun k1 k2 ->
  let c = ref 0 in
  eq_kind c k1 k2

let eq_term : term -> term -> bool = fun t1 t2 ->
  let c = ref 0 in
  eq_term c t1 t2

let eq_ordinal : ordinal -> ordinal -> bool = fun o1 o2 ->
  let c = ref 0 in
  eq_ordinal c o1 o2

(****************************************************************************
 *                                 Ordinals                                 *
 ****************************************************************************)

let rec leq_ordinal o1 o2 =
  if o1 == o2 || eq_ordinal o1 o2 then true else

  match (o1, o2) with
  | (_            , ODumm       ) -> assert false
  | (_            , OConv       ) -> true
  | (OLess(o1,_,_), o2          )
  | (OLEqu(o1,_,_), o2          ) -> leq_ordinal o1 o2
  | (_            , _           ) -> false

let rec less_ordinal o1 o2 =
  match o1 with
  | ODumm        -> assert false
  | OLess(o,_,_) -> leq_ordinal  o o2
  | OLEqu(o,_,_) -> less_ordinal o o2
  | _            -> false

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
type kvar = kind variable
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
let rec repr : kind -> kind = function
  | UVar { uvar_val = Some k} -> repr k
  | k      -> k

let set v k =
  assert (v.uvar_val = None);
  v.uvar_val <- Some k

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

let fall : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> FAll(b)) (vbind mk_free_tvar x f)

let exis : string -> (kvar -> kbox) -> kbox =
  fun x f ->
    box_apply (fun b -> Exis(b)) (vbind mk_free_tvar x f)

let tdef : type_def -> kbox array -> kbox =
  fun td ks -> box_apply2 (fun td ks -> TDef(td,ks)) (box td) (box_array ks)

let fixn : string -> ?ordinal:ordinal -> (kvar -> kbox) -> kbox =
  fun x ?(ordinal=OConv) f ->
    let b = vbind mk_free_tvar x f in
    box_apply (fun b -> FixN(ordinal,b)) b

let fixm : string -> ?ordinal:ordinal -> (kvar -> kbox) -> kbox =
  fun x ?(ordinal=OConv) f ->
    let b = vbind mk_free_tvar x f in
    box_apply (fun b -> FixM(ordinal,b)) b

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
  let reset = [reset_ucst; reset_ecst; reset_uvar] in
  List.iter (fun x -> x ()) reset

(****************************************************************************
 *                     Definition of widely used types                      *
 ****************************************************************************)

let fix_kind : kind =
  unbox (fall "X" (fun x -> func (func (box_of_var x) (box_of_var x)) (box_of_var x)))

let bot : kind =
  unbox (fall "X" (fun x -> box_of_var x))

let top : kind =
  unbox (exis "X" (fun x -> box_of_var x))

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

let case_p : pos -> term -> (string * term) list -> term =
  fun p t cs -> in_pos p (Case(t,cs))

let vdef_p : pos -> value_def -> term =
  fun p v -> in_pos p (VDef(v))

let prnt_p : pos -> string -> term =
  fun p s -> in_pos p (Prnt(s))

let fixy_p : pos -> term -> term =
  fun p t -> in_pos p (FixY(t))

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

let idt : tbox =
  labs dummy_position None (dummy_pos "x") (fun x -> x)

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

let fixy : pos -> tbox -> tbox =
  fun p t -> box_apply (fixy_p p) t

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
  let rec aux occ acc k =
    match repr k with
    | TVar(x)   -> acc
    | Func(a,b) -> aux (neg occ) (aux occ acc b) a
    | Prod(ks)
    | DSum(ks)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc ks
    | FAll(f)
    | Exis(f)   -> aux occ acc (subst f dummy)
    | FixM(_,f)
    | FixN(_,f) -> aux occ acc (subst f dummy) (* FIXME is that right ? *)
    | TDef(d,a) -> aux occ acc (msubst d.tdef_value a)
    | UCst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux2 (aux InEps acc a) c.qcst_wit_term
    | ECst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux2 (aux InEps acc a) c.qcst_wit_term
    | UVar(u)   -> if u.uvar_key = i then combine acc occ else acc
    | TInt(_)   -> assert false
  and aux2 acc t = match t.elt with
    | Cnst(t,k1,k2) -> aux2 (aux InEps (aux InEps acc k1) k2) (subst t (dummy_pos (Reco [])))
    | Coer(t,_)
    | Proj(t,_)
    | Cons(_,t)
    | FixY(t)       -> aux2 acc t
    | LAbs(_,f)     -> aux2 acc (subst f (dummy_pos (Reco [])))
    | Appl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | Reco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | Case(t,l)     -> List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | LVar _
    | VDef _
    | Prnt _
    | TagI _        -> acc

  in aux Pos Non k

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
      | FAll(f)   -> fall (binder_name f) (fun x -> fn (subst f (TVar x)))
      | Exis(f)   -> exis (binder_name f) (fun x -> fn (subst f (TVar x)))
      | FixM(o,f) -> fixm (binder_name f) ~ordinal:o (fun x -> fn (subst f (TVar x)))
      | FixN(o,f) -> fixn (binder_name f) ~ordinal:o (fun x -> fn (subst f (TVar x)))
      | UVar(u)   -> assert(u.uvar_val = None); if u.uvar_key = i then x else box k
      | TVar x    -> box_of_var x
      | t         -> box t
    in
    fn k))

(****************************************************************************
 *                    Decompostiion type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

let contract_mu = ref true
let is_mu f = !contract_mu &&
  match subst f (Prod []) with FixM(o,_) -> o = OConv | _ -> false
let is_nu f = !contract_mu &&
  match subst f (Prod []) with FixN(o,_) -> o = OConv | _ -> false

let decompose : bool -> kind -> kind * ordinal list = fun pos k ->
  let res = ref [] in
  let rec fn pos k =
    match repr k with
    | Func(a,b) -> func (fn (not pos) a) (fn pos b)
    | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | FAll(f)   -> fall (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | Exis(f)   -> exis (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | FixM(OConv,f) when is_mu f ->
       let aux x =
         match subst f x with
         | FixM(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       fn pos (FixM(OConv, f))
    | FixN(OConv,f) when is_nu f ->
       let aux x =
         match subst f x with
         | FixN(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       fn pos (FixN(OConv, f))
    | FixM(o,f) ->  if not pos then res := o :: !res else assert (o = OConv);
                   fixm (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | FixN(o,f) -> if pos then res := o :: !res else assert (o = OConv);
                   fixn (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | TVar x    -> box_of_var x
    | t         -> box t
  in
  let k = unbox (fn pos k) in
  k, (List.rev !res)

let recompose : bool -> kind -> ordinal list -> kind = fun pos k os ->
  let os = ref os in
  let get () = match !os with
      [] -> assert false
    | x::l -> os := l; x
  in
  let rec fn pos k =
    match repr k with
    | Func(a,b) -> func (fn (not pos) a) (fn pos b)
    | Prod(fs)  -> prod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | DSum(cs)  -> dsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | FAll(f)   -> fall (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | Exis(f)   -> exis (binder_name f) (fun x -> fn pos (subst f (TVar x)))
    | FixM(o,f) ->
       let ordinal = if not pos then get () else o in
       fixm (binder_name f) ~ordinal (fun x -> fn pos (subst f (TVar x)))
    | FixN(o,f) ->
       let ordinal = if pos then get () else o in
       fixn (binder_name f) ~ordinal (fun x -> fn pos (subst f (TVar x)))
    | TVar x    -> box_of_var x
    | t         -> box t
  in
  let k = unbox (fn pos k) in
  assert (!os = []);
  k
