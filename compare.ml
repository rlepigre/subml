open Ast
open Bindlib
open Position
open Term

(****************************************************************************
 *                  Function dealing with ordinal variables                 *
 ****************************************************************************)
let eq_ouvar : ouvar -> ouvar -> bool =
  fun o1 o2 -> o1.ouvar_key = o2.ouvar_key

(****************************************************************************
 *                  Equality of types, terms and ordinals                   *
 ****************************************************************************)

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

let strict f a =
  let save = !eq_strict in
  eq_strict := true;
  let res = Timed.pure_test f a in
  eq_strict := save;
  res

let set_kuvar v k =
  assert (!(v.kuvar_val) = None && !(v.kuvar_state) = Free);
  assert (mbinder_arity k = v.kuvar_arity);
  Io.log_uni "set ?%d <- %a\n\n%!"
    v.kuvar_key (!fprint_kind false)
    (msubst k (Array.init v.kuvar_arity (fun i -> free_of (new_ovari ("a_"^string_of_int i))))) ;
  Timed.(v.kuvar_val := Some k)

let fbind_ordinals  : (ordinal array -> kind -> (ordinal, kind) mbinder) ref
    = ref (fun _ -> assert false)
let fobind_ordinals : (ordinal array -> ordinal -> (ordinal, ordinal) mbinder) ref
    = ref (fun _ -> assert false)

let rec eq_kind : ordinal list -> int ref -> kind -> kind -> bool = fun pos c k1 k2 ->
  let rec eq_kind k1 k2 =
    Io.log_ord "%a = %a %b\n%!" (!fprint_kind false) k1 (!fprint_kind false) k2 !eq_strict;
    k1 == k2 || match (full_repr k1, full_repr k2) with
    | (KVari(x1)   , KVari(x2)   ) -> eq_variables x1 x2
    | (KFunc(a1,b1), KFunc(a2,b2)) -> eq_kind a1 a2 && eq_kind b1 b2
    | (KProd(fs1)  , KProd(fs2)  ) -> eq_assoc eq_kind fs1 fs2
    | (KDSum(cs1)  , KDSum(cs2)  ) -> eq_assoc eq_kind cs1 cs2
    | (KKAll(b1)   , KKAll(b2)   )
    | (KKExi(b1)   , KKExi(b2)   ) -> eq_kbinder pos c b1 b2
    | (KOAll(b1)   , KOAll(b2)   )
    | (KOExi(b1)   , KOExi(b2)   ) -> eq_obinder pos c b1 b2
    | (KFixM(o1,f1), KFixM(o2,f2))
    | (KFixN(o1,f1), KFixN(o2,f2)) -> eq_ordinal pos c o1 o2 && eq_kbinder pos c f1 f2
    | (KDPrj(t1,s1), KDPrj(t2,s2)) -> s1 = s2 && eq_term pos c t1 t2
    | (KWith(a1,e1), KWith(a2,e2)) -> let (s1,b1) = e1 and (s2,b2) = e2 in
                                      eq_kind a1 a2 && s1 = s2 &&
                                      eq_kind b1 b2
    | (KUCst(t1,f1), KUCst(t2,f2))
    | (KECst(t1,f1), KECst(t2,f2)) -> eq_kbinder pos c f1 f2 && eq_term pos c t1 t2
    | (KTInt(i1)   , KTInt(i2)   ) -> i1 = i2
    | (KMRec(p,a1) , KMRec(q,a2) )
    | (KNRec(p,a1) , KNRec(q,a2) ) -> p == q && eq_kind a1 a2
    | (KUVar(u1,o1), KUVar(u2,o2)) -> eq_kuvar u1 u2 && eq_ordinals pos c o1 o2
    | (KUVar(u1,o1), b           ) when not !eq_strict && kuvar_occur ~safe_ordinals:o1 u1 b = Non && !(u1.kuvar_state) = Free ->
       set_kuvar u1 (!fbind_ordinals o1 b); true
    | (a           , KUVar(u2,o2)) when not !eq_strict && kuvar_occur ~safe_ordinals:o2 u2 a = Non && !(u2.kuvar_state) = Free ->
       set_kuvar u2 (!fbind_ordinals o2 a); true
    | (_           , _           ) -> false
  in
  eq_kind k1 k2

and eq_kuvar : kuvar -> kuvar -> bool =
  fun v1 v2 -> v1.kuvar_key = v2.kuvar_key

and eq_ordinals =
  fun pos c o1 o2 ->
    try
      if Array.length o1 <> Array.length o2 then raise Exit;
      Array.iteri (fun i o ->
        if not (eq_ordinal pos c o o2.(i)) then raise Exit)
        o1;
      true
    with
      Exit -> false

and eq_kbinder pos c f1 f2 = f1 == f2 ||
  let i = incr c; KTInt(!c) in
  eq_kind pos c (subst f1 i) (subst f2 i)

and eq_obinder pos c f1 f2 = f1 == f2 ||
  let i = free_of (new_ovari "o") in
  eq_kind pos c (subst f1 i) (subst f2 i)

and eq_tbinder pos c f1 f2 = f1 == f2 ||
  let i = incr c; TTInt(!c) in
  eq_term pos c (subst f1 i) (subst f2 i)

and eq_term : ordinal list -> int ref -> term -> term -> bool = fun pos c t1 t2 ->
  let rec eq_term t1 t2 =
    t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (TCoer(t1,_)    , _              ) -> eq_term t1 t2
    | (_              , TCoer(t2,_)    ) -> eq_term t1 t2
    | (TDefi(d1)      , _              ) -> eq_term d1.value t2
    | (_              , TDefi(d2)      ) -> eq_term t1 d2.value
    | (TKAbs(f)       , _              ) -> eq_term (subst f (KProd[])) t2
    | (_              , TKAbs(f)       ) -> eq_term t1 (subst f (KProd[]))
    | (TOAbs(f)       , _              ) -> eq_term (subst f OConv) t2
    | (_              , TOAbs(f)       ) -> eq_term t1 (subst f OConv)
    | (TVari(x1)      , TVari(x2)      ) -> eq_variables x1 x2
    | (TAbst(_,f1)    , TAbst(_,f2)    )
    | (TFixY(_,_,f1)  , TFixY(_,_,f2)  ) -> eq_tbinder pos c f1 f2
    | (TAppl(t1,u1)   , TAppl(t2,u2)   ) -> eq_term t1 t2 && eq_term u1 u2
    | (TReco(fs1)     , TReco(fs2)     ) -> eq_assoc eq_term fs1 fs2
    | (TProj(t1,l1)   , TProj(t2,l2)   ) -> l1 = l2 && eq_term t1 t2
    | (TCons(c1,t1)   , TCons(c2,t2)   ) -> c1 = c2 && eq_term t1 t2
    | (TCase(t1,l1,d1), TCase(t2,l2,d2)) -> eq_term t1 t2 &&
                                            eq_assoc eq_term l1 l2 &&
                                            eq_option eq_term d1 d2
    | (TPrnt(s1)      , TPrnt(s2)      ) -> s1 = s2
    | (TCnst(c1)      , TCnst(c2)      ) -> eq_tcnst pos c c1 c2
    | (_              , _              ) -> false
  in eq_term t1 t2

and eq_tcnst pos c (f1,a1,b1) (f2,a2,b2) =
  eq_tbinder pos c f1 f2 && eq_kind pos c a1 a2 && eq_kind pos c b1 b2

and optpr ff = function
  | None -> ()
  | Some o -> !fprint_ordinal false ff o

and eq_ordinal : ordinal list -> int ref -> ordinal -> ordinal -> bool = fun pos c o1 o2 ->
  Io.log_ord "%a = %a %b\n%!" (!fprint_ordinal false) o1 (!fprint_ordinal false) o2 !eq_strict;
  match (orepr o1, orepr o2) with
  | (o1         , o2         ) when o1 == o2 -> true
  | (OUVar(v1,o1), OUVar(v2,o2)) when eq_ouvar v1 v2 ->  eq_ordinals pos c o1 o2
  | (OUVar(p,o1), o2         ) when not !eq_strict && not (ouvar_occur ~safe_ordinals:o1 p o2) &&
      Timed.pure_test (fun () -> set_ouvar p  (!fobind_ordinals o1 o2); less_opt_ordinal pos c o2 (p.ouvar_bnd)) () ->
     true
  | (o1         , OUVar(p,o2)   ) when not !eq_strict && not (ouvar_occur ~safe_ordinals:o2 p o1) &&
      Timed.pure_test (fun () -> set_ouvar p (!fobind_ordinals o2 o1); less_opt_ordinal pos c o1 p.ouvar_bnd) () ->
     true
  | (OConv       , OConv       ) -> true
  | (OLess(o1,w1), OLess(o2,w2)) -> eq_ordinal pos c o1 o2 && eq_ord_wit pos c w1 w2
  | (OSucc(o1)   , OSucc(o2)   ) -> eq_ordinal pos c o1 o2
  | (_           , _           ) -> false

and eq_ord_wit pos c w1 w2 = match wrepr w1, wrepr w2 with
  | (w1           , w2           ) when w1 == w2 -> true
  | (In(t1,f1)    , In(t2,f2)    )
  | (NotIn(t1,f1) , NotIn(t2,f2) ) ->
     eq_term pos c t1 t2 && eq_obinder pos c f1 f2
  | (Gen(n1,r1,f1), Gen(n2,r2,f2)) -> n1 = n2 && r1 = r2 (* FIXME: sort r1 ? *)
     && (f1 == f2 ||
           mbinder_arity f1 == mbinder_arity f2 &&
           let os = Array.init (mbinder_arity f1) (fun _ -> free_of (new_ovari "o")) in
           let (k1,k1') = msubst f1 os in
           let (k2,k2') = msubst f2 os in
           eq_kind pos c k1 k2 && eq_kind pos c k1' k2')
  | (Link p      , w           )
  | (w           , Link p      ) -> p := Some w; true (* FIXME occur check *)
  | (_           , _           ) -> false

and leqi_ordinal pos c o1 i o2 =
  Io.log_ord "%a <_%d %a %b\n%!" (!fprint_ordinal false) o1 i (!fprint_ordinal false) o2 !eq_strict;
  match (orepr o1, orepr o2) with
  | (o1         , o2      ) when i <= 0 && Timed.pure_test (eq_ordinal pos c o1) o2 -> true
  | (OLess(o1,_),       o2  ) when i > 0 && List.exists (strict_eq_ordinal o1) pos ->
     leqi_ordinal pos c o1 (i-1) o2
  | (o1         , OUVar(p,o2)) when not !eq_strict && not (ouvar_occur ~safe_ordinals:o2 p o1) &&
      Timed.pure_test (fun () -> let o1 = oadd o1 i in
                                 set_ouvar p (!fobind_ordinals o2 o1); less_opt_ordinal pos c o1 p.ouvar_bnd) () ->
     true
  | (OUVar(p,o1)   , o2      ) when not !eq_strict && i <= 0 && not (ouvar_occur ~safe_ordinals:o1 p o2) &&
      Timed.pure_test (fun () -> set_ouvar p (!fobind_ordinals o1 o2); less_opt_ordinal pos c o2 p.ouvar_bnd) () ->
     (* NOTE: may take the maximum n between 0 and -i s.t. oadd o2 n < o *)
     true
  | (OSucc o1   ,       o2  ) -> leqi_ordinal pos c o1 (i+1) o2
  | (o1         , OSucc o2  ) -> leqi_ordinal pos c o1 (i-1) o2
  | (OLess(o1,_),       o2  ) ->
     let i = if List.exists (Timed.pure_test (eq_ordinal pos c o1)) pos then i-1 else i in
     leqi_ordinal pos c o1 i o2
  | (_          , _         ) -> false

and leq_ordinal pos c o1 o2 =
  leqi_ordinal pos c o1 0 o2

and less_ordinal pos c o1 o2 =
  leqi_ordinal pos c o1 1 o2

and less_opt_ordinal pos c o1 = function
  | None -> true
  | Some o2 -> less_ordinal pos c o1 o2

and strict_eq_kind : kind -> kind -> bool =
  fun k1 k2 -> strict (eq_kind [] (ref 0) k1) k2

and strict_eq_kbinder : (kind, kind) binder -> (kind, kind) binder -> bool =
  fun f1 f2 -> strict (eq_kbinder [] (ref 0) f1) f2

and strict_eq_term : term -> term -> bool =
  fun t1 t2 -> strict (eq_term [] (ref 0) t1) t2

and strict_eq_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> strict (eq_ordinal [] (ref 0) t1) t2

and strict_eq_ord_wit : ord_wit -> ord_wit -> bool =
  fun t1 t2 -> strict (eq_ord_wit [] (ref 0) t1) t2

(****************************************************************************
 *                 Occurence test for unification variables                 *
 ****************************************************************************)

(* FIXME: should memoize this function, because a lot of sub-term are shared
   and we traverse all constants ... One could also precompute the
   variance of definitions to avoid substitution *)
and gen_occur :
    ?safe_ordinals:ordinal array -> ?kuvar:(kuvar -> bool) -> ?ouvar:(ouvar -> bool) ->
                                         unit -> (kind -> occur) * (ordinal -> occur) =
  fun ?(safe_ordinals=[||]) ?(kuvar=fun _ -> false) ?(ouvar=fun _ -> false) () ->
   let safe_ordinals = Array.to_list safe_ordinals in
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
    | KDefi(d,o,a) ->
       let acc = ref acc in
       Array.iteri (fun i o ->
         acc := aux3 !acc o) o;
       Array.iteri (fun i k ->
         acc := aux (compose occ d.tdef_kvariance.(i)) !acc k) a;
       !acc
    | KUCst(t,f)
    | KECst(t,f) -> let a = subst f kdummy in aux2 (aux Eps acc a) t
    | KUVar(u,os) -> if kuvar u then combine acc occ else Array.fold_left aux3 acc os
    | KTInt(_)   -> acc
    | KMRec(_,k)
    | KNRec(_,k) -> aux occ acc k)
  and aux2 acc t =
    if List.memq t.elt !adone_t then acc else (
    adone_t := t.elt :: !adone_t;
    match t.elt with
    | TCnst(t,k1,k2) -> aux2 (aux Eps (aux Eps acc k1) k2) (subst t (TReco []))
    | TCoer(t,_)
    | TProj(t,_)
    | TCons(_,t)     -> aux2 acc t
    | TFixY(_,_,f)
    | TAbst(_,f)     -> aux2 acc (subst f (TReco []))
    | TKAbs(f)       -> aux2 acc (subst f (KProd []))
    | TOAbs(f)       -> aux2 acc (subst f OConv)
    | TAppl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | TReco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | TCase(t,l,d)   ->
       let acc = match d with None -> acc | Some t -> aux2 acc t in
       List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | TVari(_)
    | TDefi(_)
    | TPrnt(_)
    | TTInt(_)       -> acc)
  and aux3 acc o =
    if List.exists (strict_eq_ordinal o) safe_ordinals || List.memq o !adone_o then
      acc
    else (
    adone_o := o :: !adone_o;
    match orepr o with
    | OLess(o,w) ->
       let acc = aux3 acc o in
       (match wrepr w with
       | In(t,f)|NotIn(t,f) -> aux Eps (aux2 acc t) (subst f odummy)
       | Gen(_,_,f) ->
          let os = Array.make (mbinder_arity f) OConv in
          let (k1,k2) = msubst f os in
          aux Eps (aux Eps acc k2) k1
       | Link _ -> acc)
    | OSucc o -> aux3 acc o
    | OUVar(({ouvar_bnd = Some o} as v), os) ->
       if ouvar v then combine Eps (aux3 acc o) else  aux3 (Array.fold_left aux3 acc os) o
    (* we keep this to ensure valid proof when simplifying useless induction
       needed because has_uvar below does no check ordinals *)
    | _             -> acc)
  in
  (fun k -> aux Pos Non k), (fun o -> aux3 Non o)

and set_ouvar v o =
  Io.log_uni "set %d <- %a\n\n%!"
    v.ouvar_key (!fprint_ordinal false)
    (msubst o (Array.init v.ouvar_arity (fun i -> free_of (new_ovari ("a_"^string_of_int i))))) ;
  assert (!(v.ouvar_val) = None);
  Timed.(v.ouvar_val := Some o)

and ouvar_occur : ?safe_ordinals:ordinal array -> ouvar -> ordinal -> bool =
  fun ?(safe_ordinals=[||]) v o ->
    (snd (gen_occur ~safe_ordinals ~ouvar:(fun w -> v.ouvar_key = w.ouvar_key) ()) o <> Non)

and ouvar_kind_occur : ?safe_ordinals:ordinal array -> ouvar -> kind -> bool =
  fun ?(safe_ordinals=[||]) v o ->
    (fst (gen_occur ~safe_ordinals ~ouvar:(fun w -> v.ouvar_key = w.ouvar_key) ()) o <> Non)

and kuvar_occur : ?safe_ordinals:ordinal array -> kuvar -> kind -> occur =
  fun ?(safe_ordinals=[||]) v k ->
    (fst (gen_occur ~safe_ordinals ~kuvar:(fun w -> v.kuvar_key = w.kuvar_key) ()) k)

and kuvar_ord_occur : ?safe_ordinals:ordinal array -> kuvar -> ordinal -> bool =
  fun ?(safe_ordinals=[||]) v o ->
    (snd (gen_occur ~safe_ordinals ~kuvar:(fun w -> v.kuvar_key = w.kuvar_key) ()) o <> Non)

let eq_kind : ordinal list -> kind -> kind -> bool =
  fun pos k1 k2 -> Timed.pure_test (eq_kind pos (ref 0) k1) k2

let eq_kbinder : ordinal list -> (kind, kind) binder -> (kind, kind) binder -> bool =
  fun pos f1 f2 -> Timed.pure_test (eq_kbinder pos (ref 0) f1) f2

let eq_term : ordinal list -> term -> term -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_term pos (ref 0) t1) t2

let eq_ordinal : ordinal list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_ordinal pos (ref 0) t1) t2

let eq_ord_wit : ordinal list -> ord_wit -> ord_wit -> bool =
  fun pos t1 t2 -> Timed.pure_test (eq_ord_wit pos (ref 0) t1) t2

let leq_ordinal : ordinal list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (leq_ordinal pos (ref 0) t1) t2

let less_ordinal : ordinal list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (less_ordinal pos (ref 0) t1) t2
