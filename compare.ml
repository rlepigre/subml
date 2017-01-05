(****************************************************************************)
(**{3           Comparison on types, terms and ordis                    }*)
(****************************************************************************)

open Ast
open Bindlib
open Position
open Term
open LibTools

(****************************************************************************)
(**{2                      General function                                }*)
(****************************************************************************)

let eq_assoc : ('b -> 'b -> bool) -> ('a * 'b) list -> ('a * 'b) list
                 -> bool = fun eq l1 l2 ->
  List.for_all (fun (k,_) -> List.mem_assoc k l2) l1 &&
  List.for_all (fun (k,_) -> List.mem_assoc k l1) l2 &&
  List.for_all (fun (k,e1) -> eq e1 (List.assoc k l2)) l1

let eq_option : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
  = fun eq o1 o2 -> match o1, o2 with
  | None, None -> true
  | Some t1, Some t2 -> eq t1 t2
  | _ -> false

let eq_strict : bool ref = ref false
(** this boolean control the fact that an equality is strict:
    i.e. it can not instanciate unification variables *)

(** make a function strict by changing and restoring [eq_strict] *)
let strict f a =
  let save = !eq_strict in
  eq_strict := true;
  (* NOTE: good idea to deactivate debugging here, loop
     with debug flag o *)
  let save_debug = !Io.debug in
  Io.debug := "";
  let res = Timed.pure_test f a in
  eq_strict := save;
  Io.debug := save_debug;
  res

let constant_mbind size k =
  unbox (mbind mk_free_ovari (Array.make size "_") (fun x -> box k))

let mbind_assoc cst size l =
  unbox (mbind mk_free_ovari (Array.make size "α")
           (fun v -> cst (List.map (fun (s,k) ->
             (s, mbind_apply (box k) (box_array v))) l)))

(****************************************************************************
 *                 setting of unification variable                          *
 ****************************************************************************)

(** function to set type variables (a more complex
    function [safe_set_kuvar] exists) *)
let set_kuvar v k =
  if !(v.uvar_val) = None then (
    assert (mbinder_arity k = v.uvar_arity);
    Io.log_uni "set ?%d <- %a\n\n%!"
      v.uvar_key (!fprint_kind false)
      (msubst k (Array.init v.uvar_arity
                   (fun i -> free_of (new_ovari ("a_"^string_of_int i))))) ;
    Timed.(v.uvar_val := Some k))

(** function to set ordi variables *)
let set_ouvar ?(msg="") v o =
  Io.log_uni "set %d <- %a (%s)\n\n%!"
    v.uvar_key (!fprint_ordi false)
    (msubst o (Array.init v.uvar_arity
                 (fun i -> free_of (new_ovari ("a_"^string_of_int i))))) msg;
  assert (!(v.uvar_val) = None);
  Timed.(v.uvar_val := Some o)

(** forward references to function binding ordis in kinds and ordinals *)
(** TODO: reorder the definition to minimize mutual recursion *)
let fbind_ordis  : (ordi array -> kind -> kind from_ordis) ref
    = ref (fun _ -> assert false)
let fobind_ordis : (ordi array -> ordi -> ordi from_ordis) ref
    = ref (fun _ -> assert false)

(****************************************************************************)
(**{2                     Ordinal comparisons                              }*)
(****************************************************************************)

let rec eq_ordis =
  fun pos o1 o2 ->
    try
      if Array.length o1 <> Array.length o2 then raise Exit;
      Array.iteri (fun i o ->
        if not (eq_ordi pos o o2.(i)) then raise Exit)
        o1;
      true
    with
      Exit -> false

and eq_obinder pos f1 f2 = f1 == f2 ||
  let i = free_of (new_ovari "o") in
  eq_kind pos (subst f1 i) (subst f2 i)

and optpr ff = function
  | None -> ()
  | Some o -> !fprint_ordi false ff o

and eq_ordi : ordi list -> ordi -> ordi -> bool = fun pos o1 o2 ->
  Io.log_ord "%a = %a %b\n%!"
    (!fprint_ordi false) o1 (!fprint_ordi false) o2 !eq_strict;
  match (orepr o1, orepr o2) with
  | (o1         , o2         ) when o1 == o2 -> true
  | (OUVar(v1,o1), OUVar(v2,o2)) when eq_uvar v1 v2 -> eq_ordis pos o1 o2
  | (OUVar(p,os), o2         ) when not !eq_strict &&
                                    not (ouvar_occur ~safe_ordis:os p o2) &&
      Timed.pure_test (fun () -> set_ouvar ~msg:"eq1" p
        (!fobind_ordis os o2); less_opt_ordi pos o2 p.uvar_state os) () ->
     (eq_ordi pos o1 o2)
  | (o1         , OUVar(p,os)   ) when not !eq_strict &&
                                       not (ouvar_occur ~safe_ordis:os p o1) &&
      Timed.pure_test (fun () -> set_ouvar ~msg:"eq2" p
        (!fobind_ordis os o1); less_opt_ordi pos o1 p.uvar_state os) () ->
     (eq_ordi pos o1 o2)
  | (OConv       , OConv       ) -> true
  | (OLess(o1,w1), OLess(o2,w2)) -> eq_ordi pos o1 o2 && eq_ord_wit pos w1 w2
  | (OSucc(o1)   , OSucc(o2)   ) -> eq_ordi pos o1 o2
  | (_           , _           ) -> false

and eq_ord_wit pos w1 w2 = match w1, w2 with
  | (w1           , w2          ) when w1 == w2 -> true
  | (In(t1,f1)    , In(t2,f2)   )
  | (NotIn(t1,f1) , NotIn(t2,f2)) -> eq_term pos t1 t2 && eq_obinder pos f1 f2
  | (Gen(n1,s1)   , Gen(n2,s2)  ) -> n1 = n2 && eq_schema pos s1 s2
  | (_            , _           ) -> false

and eq_schema pos s1 s2 =
  s1.sch_posit = s2.sch_posit (* FIXME: sort ? *)
  && s1.sch_relat = s2.sch_relat
  && (let f1 = s1.sch_judge and f2 = s2.sch_judge in
      f1 == f2 ||
        mbinder_arity f1 == mbinder_arity f2 &&
        let os = Array.init (mbinder_arity f1) (fun _ -> free_of (new_ovari "o")) in
        let (k1,k1') = msubst f1 os in
        let (k2,k2') = msubst f2 os in
        eq_term_or_kind pos k1 k2 && eq_kind pos k1' k2')

and eq_term_or_kind pos x1 x2 = match (x1,x2) with
    SchTerm t1, SchTerm t2 -> eq_term pos t1 t2
  | SchKind k1, SchKind k2 -> eq_kind pos k1 k2
  | _         , _          -> false

and leqi_ordi pos o1 i o2 =
  Io.log_ord "%a <_%d %a %b\n%!"
    (!fprint_ordi false) o1 i (!fprint_ordi false) o2 !eq_strict;
  match (orepr o1, orepr o2) with
  | (o1         , o2      ) when i <= 0 && strict_eq_ordi o1 o2 -> true
  | (OLess(o1,_),       o2  ) when i > 0 && List.exists (strict_eq_ordi o1) pos ->
     leqi_ordi pos o1 (i-1) o2
  | (o1         , OSucc o2  ) -> leqi_ordi pos o1 (i-1) o2
  | (OSucc o1   ,       o2  ) -> leqi_ordi pos o1 (i+1) o2
  | (OUVar({uvar_state = (_, Some o')},os),       o2  )
       when strict (leqi_ordi pos (msubst o' os) (i-1)) o2 ->
    true
  | (OUVar({uvar_state = (Some o',_)} as p,os),       o2  ) ->
     set_ouvar ~msg:"leq3" p o';
     leqi_ordi pos o1 i o2
  | (OUVar(p,os)   , o2      ) when i<=0 && not !eq_strict &&
      not (ouvar_occur ~safe_ordis:os p o2) &&
      Timed.pure_test (fun () -> less_opt_ordi pos o2 p.uvar_state os) () ->
     let o2' = new_ouvar
       ?lower:(match fst p.uvar_state with
           | None -> None
           | Some f -> Some (constant_mbind 0 (msubst f os)))
       ~upper:(constant_mbind 0 o2) () in
     let f = !fobind_ordis os o2' in
     set_ouvar ~msg:"leq1" p f;
     leq_ordi pos (msubst f os) o2'
  | (o1         , OUVar(p,os)) when not !eq_strict &&
                                    not (ouvar_occur ~safe_ordis:os p o1) &&
      Timed.pure_test (fun () ->
        let o1 = oadd o1 i in
        less_opt_ordi pos o1 p.uvar_state os) () ->
     let general = match orepr o1 with
         OLess(OConv,_) -> false
       | OLess(o,_) ->
          (match snd p.uvar_state with
              None -> true
            | Some f -> not (strict_eq_ordi (msubst f os) o))
       | _ -> false
     in
     let o1' = oadd o1 i in
     let o1' =
       if general then
         new_ouvar
           ~lower:(constant_mbind 0 o1')
           ?upper:(match snd p.uvar_state with
           | None -> None
           | Some f -> Some (constant_mbind 0 (msubst f os))) ()
       else o1'
     in
     let f = !fobind_ordis os o1' in
     set_ouvar ~msg:"leq2" p f;
    leq_ordi pos o1' (msubst f os)
  | (OLess(o1,_),       o2  ) ->
     let i = if List.exists (Timed.pure_test (eq_ordi pos o1)) pos then i-1 else i in
     leqi_ordi pos o1 i o2
  | (_          , _         ) -> false

and leq_ordi pos o1 o2 =
  leqi_ordi pos o1 0 o2

and less_ordi pos o1 o2 =
  leqi_ordi pos o1 1 o2

and less_opt_ordi pos o1 (lower,upper) os =
  (match upper with
  | None -> true
  | Some f ->
    assert (mbinder_arity f = Array.length os);
    let o2 = msubst f os in
    less_ordi pos o1 o2) &&
  (match lower with
  | None -> true
  | Some f ->
    assert (mbinder_arity f = Array.length os);
    let o2 = msubst f os in
    leq_ordi pos o2 o1)


(****************************************************************************)
(**{2                     Equality on kinds                                }*)
(****************************************************************************)

and eq_kind : ordi list -> kind -> kind -> bool = fun pos k1 k2 ->
  let rec eq_kind k1 k2 =
    Io.log_ord "%a = %a %b\n%!"
      (!fprint_kind false) k1 (!fprint_kind false) k2 !eq_strict;
    k1 == k2 || match (full_repr k1, full_repr k2) with
    | (KVari(x1)   , KVari(x2)   ) -> eq_variables x1 x2
    | (KFunc(a1,b1), KFunc(a2,b2)) -> eq_kind a1 a2 && eq_kind b1 b2
    | (KProd(fs1)  , KProd(fs2)  ) -> eq_assoc eq_kind fs1 fs2
    | (KDSum(cs1)  , KDSum(cs2)  ) -> eq_assoc eq_kind cs1 cs2
    | (KKAll(b1)   , KKAll(b2)   )
    | (KKExi(b1)   , KKExi(b2)   ) -> eq_kbinder pos b1 b2
    | (KOAll(b1)   , KOAll(b2)   )
    | (KOExi(b1)   , KOExi(b2)   ) -> eq_obinder pos b1 b2
    | (KFixM(o1,f1), KFixM(o2,f2))
    | (KFixN(o1,f1), KFixN(o2,f2)) -> eq_kbinder pos f1 f2 && eq_ordi pos o1 o2
    | (KUCst(t1,f1,_), KUCst(t2,f2,_))
    | (KECst(t1,f1,_), KECst(t2,f2,_)) -> eq_kbinder pos f1 f2 && eq_term pos t1 t2
    | (KMRec(p,a1) , KMRec(q,a2) )
    | (KNRec(p,a1) , KNRec(q,a2) ) -> p == q && eq_kind a1 a2
    | (KUVar(u1,o1), KUVar(u2,o2)) -> eq_uvar u1 u2 && eq_ordis pos o1 o2
    | (KUVar(u1,o1), b           ) when not !eq_strict &&
                                        kuvar_occur ~safe_ordis:o1 u1 b = Non
                                        && !(u1.uvar_state) = Free ->
       set_kuvar u1 (!fbind_ordis o1 b); eq_kind k1 k2
    | (a           , KUVar(u2,o2)) when not !eq_strict &&
                                        kuvar_occur ~safe_ordis:o2 u2 a = Non
                                        && !(u2.uvar_state) = Free ->
       set_kuvar u2 (!fbind_ordis o2 a); eq_kind k1 k2
    | (KPrnt s1    , KPrnt s2    ) -> s1 = s2
    | (_           , _           ) -> false
  in
  eq_kind k1 k2


and eq_kbinder pos f1 f2 = f1 == f2 ||
  let i = free_of (new_kvari "X") in
  eq_kind pos (subst f1 i) (subst f2 i)

and eq_tkbinder pos f1 f2 = f1 == f2 ||
  let i = free_of (new_tvari "t") in
  eq_kind pos (subst f1 i) (subst f2 i)

(****************************************************************************)
(**{2                     Equality on terms                                }*)
(****************************************************************************)

and eq_term : ordi list -> term -> term -> bool = fun pos t1 t2 ->
  let rec eq_term t1 t2 =
    t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (TCoer(t1,_)    , _              ) -> eq_term t1 t2
    | (_              , TCoer(t2,_)    ) -> eq_term t1 t2
    | (TDefi(d1)      , _              ) -> eq_term d1.value t2
    | (_              , TDefi(d2)      ) -> eq_term t1 d2.value
    | (TMLet(_,_,t1)  , _              ) -> eq_term (mmsubst_dummy t1 OConv (KProd [])) t2
    | (_              , TMLet(_,_,t2)  ) -> eq_term t1 (mmsubst_dummy t2 OConv (KProd []))
    | (TVari(x1)      , TVari(x2)      ) -> eq_variables x1 x2
    | (TVars(s1)      , TVars(s2)      ) -> s1 = s2
    | (TAbst(_,f1)    , TAbst(_,f2)    )
    | (TFixY(_,_,f1)  , TFixY(_,_,f2)  ) -> eq_tbinder pos f1 f2
    | (TAppl(t1,u1)   , TAppl(t2,u2)   ) -> eq_term t1 t2 && eq_term u1 u2
    | (TReco(fs1)     , TReco(fs2)     ) -> eq_assoc eq_term fs1 fs2
    | (TProj(t1,l1)   , TProj(t2,l2)   ) -> l1 = l2 && eq_term t1 t2
    | (TCons(c1,t1)   , TCons(c2,t2)   ) -> c1 = c2 && eq_term t1 t2
    | (TCase(t1,l1,d1), TCase(t2,l2,d2)) -> eq_term t1 t2 &&
                                            eq_assoc eq_term l1 l2 &&
                                            eq_option eq_term d1 d2
    | (TPrnt(s1)      , TPrnt(s2)      ) -> s1 = s2
    | (TCnst(f1,a1,b1), TCnst(f2,a2,b2)) -> eq_tcnst pos f1 a1 b1 f2 a2 b2
    | (_              , _              ) -> false
  in eq_term t1 t2

and eq_tbinder pos f1 f2 = f1 == f2 ||
  let i = free_of (new_tvari "x") in
  eq_term pos (subst f1 i) (subst f2 i)

and eq_tcnst pos f1 a1 b1 f2 a2 b2 =
  eq_tbinder pos f1 f2 && eq_kind pos a1 a2 && eq_kind pos b1 b2

(****************************************************************************)
(**{2                     Strict equalities                                }*)
(****************************************************************************)

and strict_eq_kind : kind -> kind -> bool =
  fun k1 k2 -> strict (eq_kind [] k1) k2

and strict_eq_kbinder : (kind, kind) binder -> (kind, kind) binder -> bool =
  fun f1 f2 -> strict (eq_kbinder [] f1) f2

and strict_eq_tkbinder : (term', kind) binder -> (term', kind) binder -> bool =
  fun f1 f2 -> strict (eq_tkbinder [] f1) f2

and strict_eq_tbinder : (term', term) binder -> (term', term) binder -> bool =
  fun f1 f2 -> strict (eq_tbinder [] f1) f2

and strict_eq_term : term -> term -> bool =
  fun t1 t2 -> strict (eq_term [] t1) t2

and strict_eq_ordi : ordi -> ordi -> bool =
  fun t1 t2 -> strict (eq_ordi [] t1) t2

and strict_eq_ord_wit : ord_wit -> ord_wit -> bool =
  fun t1 t2 -> strict (eq_ord_wit [] t1) t2

and strict_leq_ordi : ordi -> ordi -> bool =
  fun t1 t2 -> strict (leq_ordi [] t1) t2

(****************************************************************************
 *                 Occurence test for unification variables                 *
 ****************************************************************************)

(* FIXME: should memoize this function, because a lot of sub-term are shared
   and we traverse all constants ... One could also precompute the
   variance of definitions to avoid substitution *)
and gen_occur :
    ?safe_ordis:ordi array -> ?kuvar:(kuvar -> bool) -> ?ouvar:(ouvar -> bool) ->
                                         unit -> (kind -> occur) * (ordi -> occur) =
  fun ?(safe_ordis=[||]) ?(kuvar=fun _ -> false) ?(ouvar=fun _ -> false) () ->
   let safe_ordis = Array.to_list safe_ordis in
  let kdummy = KProd [] in
  let odummy = OConv in
  let adone_k = ref [] in
  let adone_t = ref [] in
  let adone_o = ref [] in
  let rec aux occ acc k =
    let k = repr k in
    if List.memq k !adone_k then acc else (
    adone_k := k :: !adone_k;
    match k with
    | KVari(x)   -> acc
    | KFunc(a,b) -> aux (neg occ) (aux occ acc b ) a
    | KProd(ks)
    | KDSum(ks)  -> List.fold_left (fun acc (_,k) -> aux occ acc k) acc ks
    | KKAll(f)
    | KKExi(f)   -> aux occ acc (subst f kdummy)
    | KOAll(f)
    | KOExi(f)   -> aux occ acc (subst f odummy)
    | KFixM(o,f)
    | KFixN(o,f) -> aux occ (aux3 acc o) (subst f kdummy)
    | KDefi(d,o,a) ->
       let acc = ref acc in
       Array.iteri (fun i o ->
         acc := aux3 !acc o) o;
       Array.iteri (fun i k ->
         acc := aux (compose occ d.tdef_kvariance.(i)) !acc k) a;
       !acc
    | KUCst(t,f,_)
    | KECst(t,f,_) -> aux2 (aux All acc (subst f kdummy)) t
    | KUVar(u,os) -> if kuvar u then combine acc occ else Array.fold_left aux3 acc os
    | KMRec(_,k) (* NOTE: safe to ignore ordis as they are not used in unif var *)
    | KNRec(_,k) -> aux occ acc k
    | KPrnt _ -> assert false)
  and aux2 acc t =
    if List.memq t.elt !adone_t then acc else (
    adone_t := t.elt :: !adone_t;
    match t.elt with
    | TCnst(t,k1,k2) -> aux2 (aux All (aux All acc k1) k2) (subst t (TReco []))
    | TCoer(t,_)
    | TProj(t,_)
    | TCons(_,t)     -> aux2 acc t
    | TMLet(b,x,bt)  -> aux2 acc (mmsubst_dummy bt OConv (KProd []))
    | TFixY(_,_,f)
    | TAbst(_,f)     -> aux2 acc (subst f (TReco []))
    | TAppl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | TReco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | TCase(t,l,d)   ->
       let acc = match d with None -> acc | Some t -> aux2 acc t in
       List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | TVari(_)
    | TVars(_)
    | TDefi(_)
    | TPrnt(_)       -> acc)
  and aux3 acc o =
    if List.exists (strict_eq_ordi o) safe_ordis || List.memq o !adone_o then
      acc
    else (
    adone_o := o :: !adone_o;
    match orepr o with
    | OLess(o,w) ->
       let acc = aux3 acc o in
       (match w with
       | In(t,f)|NotIn(t,f) -> aux All (aux2 acc t) (subst f odummy)
       | Gen(_,s) ->
          let f = s.sch_judge in
          let os = Array.make (mbinder_arity f) OConv in
          let (k1,k2) = msubst f os in
          aux5 (aux All acc k2) k1)
    | OSucc o -> aux3 acc o
    | OUVar(({uvar_state = o} as v), os) ->
       if ouvar v then combine All (aux4 acc os o)
       else aux4 (Array.fold_left aux3 acc os) os o
       (* we keep this to ensure valid proof when simplifying useless induction
         needed because has_uvar below does no check ordis *)
    | _             -> acc)
  and aux4 acc os (lower, upper) =
    let acc = match lower with
    | None -> acc
    | Some f -> aux3 acc (msubst f os)
    in
    let acc = match upper with
    | None -> acc
    | Some f -> aux3 acc (msubst f os)
    in
    acc
  and aux5 acc = function
    | SchTerm t -> aux2    acc t
    | SchKind k -> aux All acc k
  in
  (fun k -> aux sPos Non k), (fun o -> aux3 Non o)

and ouvar_occur : ?safe_ordis:ordi array -> ouvar -> ordi -> bool =
  fun ?(safe_ordis=[||]) v o ->
    snd (gen_occur ~safe_ordis ~ouvar:(fun w -> v.uvar_key = w.uvar_key) ()) o <> Non

and ouvar_kind_occur : ?safe_ordis:ordi array -> ouvar -> kind -> bool =
  fun ?(safe_ordis=[||]) v o ->
    (fst (gen_occur ~safe_ordis ~ouvar:(fun w -> v.uvar_key = w.uvar_key) ()) o <> Non)

and kuvar_occur : ?safe_ordis:ordi array -> kuvar -> kind -> occur =
  fun ?(safe_ordis=[||]) v k ->
    (fst (gen_occur ~safe_ordis ~kuvar:(fun w -> v.uvar_key = w.uvar_key) ()) k)

and kuvar_ord_occur : ?safe_ordis:ordi array -> kuvar -> ordi -> bool =
  fun ?(safe_ordis=[||]) v o ->
    (snd (gen_occur ~safe_ordis ~kuvar:(fun w -> v.uvar_key = w.uvar_key) ()) o <> Non)

(****************************************************************************)
(**{2                     Protection of tests                              }*)
(****************************************************************************)

let eq_kind : ordi list -> kind -> kind -> bool =
  fun pos k1 k2 -> Timed.pure_test (eq_kind pos k1) k2

let eq_kbinder : ordi list -> (kind, kind) binder -> (kind, kind) binder -> bool =
  fun pos f1 f2 -> Timed.pure_test (eq_kbinder pos f1) f2

let eq_tkbinder : ordi list -> (term', kind) binder -> (term', kind) binder -> bool =
  fun pos f1 f2 -> Timed.pure_test (eq_tkbinder pos f1) f2

let eq_term : ordi list -> term -> term -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_term pos t1) t2

let eq_ordi : ordi list -> ordi -> ordi -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_ordi pos t1) t2

let eq_ord_wit : ordi list -> ord_wit -> ord_wit -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_ord_wit pos t1) t2

let leq_ordi : ordi list -> ordi -> ordi -> bool =
  fun pos t1 t2 -> Timed.pure_test (leq_ordi pos t1) t2

let less_ordi : ordi list -> ordi -> ordi -> bool =
  fun pos t1 t2 -> Timed.pure_test (less_ordi pos t1) t2

(****************************************************************************)
(**{2                     Searching functions                              }*)
(****************************************************************************)

let assoc_ordi o l = assoc_gen strict_eq_ordi o l
let assoc_kind k l = assoc_gen strict_eq_kind k l
let assoc_term t l = assoc_gen strict_eq_term t l
let assoc_tterm k l = assoc_gen strict_eq_tbinder k l
let assoc_tkind k l = assoc_gen strict_eq_tkbinder k l
let assoc_kkind k l = assoc_gen strict_eq_kbinder k l
