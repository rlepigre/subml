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
  (* Bounded quantifiers: ∀/∃X [= A] [</> B] C. *)
  | FAll of kind option * (orient * kind) option * (kind, kind) binder
  | Exis of kind option * (orient * kind) option * (kind, kind) binder
  (* Least and greatest fixpoint: μX A, νX A. *)
  | FixM of (kind, kind) binder
  | FixN of (kind, kind) binder
  (* User-defined type applied to arguments: T(A1,...,An). *)
  | TDef of type_def * kind array
  (**** Special constructors (not accessible to user) ****)
  (* Constants (a.k.a. epsilon) - used for subtyping. *)
  | UCst of qcst
  | ECst of qcst
  | MCst of fcst
  | NCst of fcst
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
  ; qcst_bound    : (orient * kind) option
  ; qcst_wit_term : term
  ; qcst_wit_kind : (kind, kind) binder }

(* Fixpoint constant. *)
and fcst =
  { fcst_key      : int
  ; fcst_level    : int list
  ; fcst_wit_kind : (kind, kind) binder }

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
  (* Constant (a.k.a. epsilon). Cnst(t[x],A,B) = u is a witness (i.e. a term)
     that has type A but not type B such that t[u] is in B. *)
  | Cnst of ((term, term) binder * kind * kind)
  
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

let fall : string -> kbox option -> (orient * kbox) option
  -> (kbox -> kbox) -> kbox =
  fun x ko bo f ->
    let bo = map_opt (fun (o,k) -> box_apply (fun k -> (o,k)) k) bo in
    let b = bind mk_free_tvar x f in
    box_apply3 (fun ko bo b -> FAll(ko,bo,b)) (box_opt ko) (box_opt bo) b

let fall' : string -> (kbox -> kbox) -> kbox =
  fun x f -> fall x None None f

let exis : string -> kbox option -> (orient * kbox) option
  -> (kbox -> kbox) -> kbox =
  fun x ko bo f ->
    let bo = map_opt (fun (o,k) -> box_apply (fun k -> (o,k)) k) bo in
    let b = bind mk_free_tvar x f in
    box_apply3 (fun ko bo b -> Exis(ko,bo,b)) (box_opt ko) (box_opt bo) b

let exis' : string -> (kbox -> kbox) -> kbox =
  fun x f -> exis x None None f

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

(* Quantifier constant management. *)
let (new_ucst, reset_ucst) =
  let c = ref 0 in
  let new_ucst t bnd f = UCst
    { qcst_key      = (incr c; !c)
    ; qcst_bound    = bnd
    ; qcst_wit_term = t
    ; qcst_wit_kind = f }
  in
  let reset_ucst () = c := 0 in
  (new_ucst, reset_ucst)

let (new_ecst, reset_ecst) =
  let c = ref 0 in
  let new_ecst t bnd f = ECst
    { qcst_key      = (incr c; !c)
    ; qcst_bound    = bnd
    ; qcst_wit_term = t
    ; qcst_wit_kind = f }
  in
  let reset_ecst () = c := 0 in
  (new_ecst, reset_ecst)

(* Fixpoint constant management. *)
let (new_mcst, reset_mcst) = (* TODO implement lookup in table. *)
  let c = ref 0 in
  let new_mcst f = MCst
    { fcst_key      = (incr c; !c)
    ; fcst_level    = []
    ; fcst_wit_kind = f }
  in
  let reset_mcst () = c := 0 in
  (new_mcst, reset_mcst)

let (new_ncst, reset_ncst) = (* TODO implement lookup in table. *)
  let c = ref 0 in
  let new_ncst f = NCst
    { fcst_key      = (incr c; !c)
    ; fcst_level    = []
    ; fcst_wit_kind = f }
  in
  let reset_ncst () = c := 0 in
  (new_ncst, reset_ncst)

let (new_level, reset_level) =
  let e = ref 0 in
  let new_level l = l @ [(incr e; !e)] in
  let reset_level = e := 0 in
  (new_level, reset_level)

(* Unification variable management. Useful for typing. *)
let (new_uvar, reset_uvar) =
  let c = ref 0 in
  let new_uvar () = UVar {uvar_key = (incr c; !c); uvar_val = None} in
  let reset_uvar () = c := 0 in
  (new_uvar, reset_uvar)

(* Resset all counters. *)
let reset_all () =
  let reset = [reset_ucst; reset_ecst; reset_mcst; reset_ncst; reset_uvar] in
  List.iter (fun x -> x ()) reset

(****************************************************************************
 *                     Definition of widely used types                      *
 ****************************************************************************)

let fix_kind : kind =
  unbox (fall' "X" (fun x -> func (func x x) x))

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

let cnst_p : pos -> ((term, term) binder * kind * kind) -> term =
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
let cnst : (term, term) binder -> kind -> kind -> term =
  fun s a b -> dummy_pos (Cnst(s,a,b))

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
    | FAll(ao,bo,f) -> aux occ acc (subst f dummy) (* FIXME bound *)
    | Exis(ao,bo,f) -> aux occ acc (subst f dummy) (* FIXME bound *)
    | FixM(f)   -> aux occ acc (subst f dummy) (* FIXME is that right ? *)
    | FixN(f)   -> aux occ acc (subst f dummy) (* FIXME is that right ? *)
    | TDef(d,a) -> aux occ acc (msubst d.tdef_value a)
    | UCst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux InEps acc a (* FIXME bnd ? *)
    | ECst(c)   -> let a = subst c.qcst_wit_kind dummy in
                   aux InEps acc a (* FIXME bnd ? *)
    | MCst(c)   -> let a = subst c.fcst_wit_kind dummy in
                   aux InEps acc a
    | NCst(c)   -> let a = subst c.fcst_wit_kind dummy in
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
    | FAll(ao,bo,f) ->
        let ao = map_opt subst ao in
        let bo = map_opt (fun (o,a) -> (o,subst a)) bo in
        FAll(ao, bo, binder_compose_right f subst)
    | Exis(ao,bo,f) ->
        let ao = map_opt subst ao in
        let bo = map_opt (fun (o,a) -> (o,subst a)) bo in
        Exis(ao, bo, binder_compose_right f subst)
    | FixM(f)   -> FixM(binder_compose_right f subst)
    | FixN(f)   -> FixN(binder_compose_right f subst)
    | TDef(d,a) -> TDef(d, Array.map subst a)
    | UCst(_)   -> assert false (* TODO *)
    | ECst(_)   -> assert false (* TODO *)
    | MCst(_)   -> assert false (* TODO *)
    | NCst(_)   -> assert false (* TODO *)
    | UVar(u)   -> if u.uvar_key = i then x else k
    | TInt(_)   -> assert false
  in
  subst k

(****************************************************************************
 *             Collecting all the unification variables of a type           *
 ****************************************************************************)

module UVarOrd =
  struct
    type t = uvar
    let compare u1 u2 = compare u1.uvar_key u2.uvar_key
  end

module UVarSet = Set.Make(UVarOrd)

let uvars : kind -> uvar list = fun k ->
  let dummy = Prod [] in
  let union = List.fold_left UVarSet.union UVarSet.empty in
  let rec uvars = function
    | TVar(_)   -> UVarSet.empty
    | Func(a,b) -> UVarSet.union (uvars a) (uvars b)
    | Prod(fs)  -> let f s (_,a) = UVarSet.union s (uvars a) in
                   List.fold_left f UVarSet.empty fs
    | FAll(ao,bo,f) ->
        let c = subst f dummy in
        begin
          match (ao, bo) with
          | (None  , None      ) -> uvars c
          | (Some a, None      ) -> union [ uvars a; uvars c ]
          | (None  , Some (_,b)) -> union [ uvars b; uvars c ]
          | (Some a, Some (_,b)) -> union [ uvars a; uvars b; uvars c ]
        end
    | Exis(ao,bo,f) ->
        let c = subst f dummy in
        begin
          match (ao, bo) with
          | (None  , None      ) -> uvars c
          | (Some a, None      ) -> union [ uvars a; uvars c ]
          | (None  , Some (_,b)) -> union [ uvars b; uvars c ]
          | (Some a, Some (_,b)) -> union [ uvars a; uvars b; uvars c ]
        end
    | FixM(f)   -> uvars (subst f dummy)
    | FixN(f)   -> uvars (subst f dummy)
    | TDef(d,a) -> let f s a = UVarSet.union s (uvars a) in
                   Array.fold_left f UVarSet.empty a
    | UCst(_)   -> assert false (* TODO *)
    | ECst(_)   -> assert false (* TODO *)
    | MCst(_)   -> assert false (* TODO *)
    | NCst(_)   -> assert false (* TODO *)
    | UVar(u)   ->
        begin
          match uvar_repr u with
          | UVar u -> UVarSet.singleton u
          | k      -> uvars k
        end
    | TInt(_)   -> assert false
  in
  UVarSet.elements (uvars k)

let rec free_names : kind -> string list = function
  | TVar(x)    -> [name_of x]
  | Func(a,b)  -> (free_names a) @ (free_names b)
  | Prod(fs)   -> List.flatten (List.map (fun (_,a) -> free_names a) fs)
  | FAll(ao,bo,f) ->
      begin
        let c = subst f (Prod []) in
        match (ao, bo) with
        | (None  , None      ) -> free_names c
        | (Some a, None      ) -> (free_names a) @ (free_names c)
        | (None  , Some (_,b)) -> (free_names b) @ (free_names c)
        | (Some a, Some (_,b)) ->
            (free_names a) @ (free_names b) @ (free_names c)
      end
  | Exis(ao,bo,f) ->
      begin
        let c = subst f (Prod []) in
        match (ao, bo) with
        | (None  , None      ) -> free_names c
        | (Some a, None      ) -> (free_names a) @ (free_names c)
        | (None  , Some (_,b)) -> (free_names b) @ (free_names c)
        | (Some a, Some (_,b)) ->
            (free_names a) @ (free_names b) @ (free_names c)
      end
  | FixM(f)    -> free_names (subst f (Prod []))
  | FixN(f)    -> free_names (subst f (Prod []))
  | TDef(d,a)  -> let l = Array.to_list (Array.map free_names a) in
                  d.tdef_name :: (List.flatten l)
  | UCst(_)    -> assert false (* TODO *)
  | ECst(_)    -> assert false (* TODO *)
  | MCst(_)    -> assert false (* TODO *)
  | NCst(_)    -> assert false (* TODO *)
  | UVar(u)    -> []
  | TInt(_)    -> assert false

let fresh_name : string -> string list -> string * string list =
  fun pref used ->
    let rec fresh i =
      let pref = Printf.sprintf "%s%i" pref i in
      if List.mem pref used then
        fresh (i+1)
      else
        (pref, pref :: used)
    in fresh 1

let generalize : kind -> kind = fun k ->
  let us = uvars k in
  let f u (k, used) =
    let (x, used) = fresh_name "X" used in
    let k =
      FAll(None, None, binder_from_fun x (fun x -> bind_uvar u k x))
    in (k, used)
  in
  fst (List.fold_right f us (k, free_names k))

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
    | (FAll(_,ba,a), FAll(_,bb,b)) ->
        let i = new_int () in
        lower_bound ba bb && lower_kind (subst a i) (subst b i)
    | (Exis(_,ba,a), FAll(_,bb,b)) ->
        let i = new_int () in
        lower_bound ba bb && lower_kind (subst a i) (subst b i)
    | (FixM(fa)    , FixM(fb)    ) ->
        let i = new_int () in
        lower_kind (subst fa i) (subst fb i)
    | (FixN(fa)    , FixN(fb)    ) ->
        let i = new_int () in
        lower_kind (subst fa i) (subst fb i)
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
    | (MCst(ca)    , MCst(cb)    ) when ca.fcst_key = cb.fcst_key ->
        leq_level ca.fcst_level cb.fcst_level
    | (MCst(ca)    , MCst(cb)    ) ->
        let i = new_int () in
        let a = subst ca.fcst_wit_kind i in
        let b = subst cb.fcst_wit_kind i in
        lower_kind a b && leq_level ca.fcst_level cb.fcst_level
    | (NCst(ca)    , NCst(cb)    ) when ca.fcst_key = cb.fcst_key ->
        leq_level cb.fcst_level ca.fcst_level
    | (NCst(ca)    , NCst(cb)    ) ->
        let i = new_int () in
        let a = subst ca.fcst_wit_kind i in
        let b = subst cb.fcst_wit_kind i in
        lower_kind a b && leq_level cb.fcst_level ca.fcst_level
    | (NCst(ca)    , MCst(cb)    ) -> false
    | (MCst(ca)    , NCst(cb)    ) -> false
    | (UVar(ua)    , UVar(ub)    ) when ua == ub -> true
    | (TInt(ia)    , TInt(ib)    ) -> ia = ib
    | (_           , _           ) -> false
  and lower_bound b1 b2 =
    match (b1, b2) with
    | (None      , None      ) -> true
    | (Some(GE,a), Some(GE,b)) -> lower_kind a b
    | (Some(LE,a), Some(LE,b)) -> lower_kind b a
    | (_         , _         ) -> false
  in lower_kind k1 k2
