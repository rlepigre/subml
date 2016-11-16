open Ast
open Bindlib
open Position

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
                                      eq_kind a1 a2 && s1 = s2 &&
                                      eq_kind b1 b2
    | (KUCst(t1,f1), KUCst(t2,f2))
    | (KECst(t1,f1), KECst(t2,f2)) -> eq_kbinder c f1 f2 && eq_term c t1 t2
    | (KUVar(u1)   , KUVar(u2)   ) -> eq_kuvar u1 u2
    | (KTInt(i1)   , KTInt(i2)   ) -> i1 = i2
    | (KMRec(p,a1) , KMRec(q,a2) )
    | (KNRec(p,a1) , KNRec(q,a2) ) -> p == q && eq_kind a1 a2
    | (_           , _           ) -> false
  in
  eq_kind k1 k2

and eq_kuvar : kuvar -> kuvar -> bool =
  fun v1 v2 -> v1.kuvar_key = v2.kuvar_key

and eq_kbinder c f1 f2 = f1 == f2 ||
  let i = incr c; KTInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_obinder c f1 f2 = f1 == f2 ||
  let i = incr c; OTInt(!c) in
  eq_kind c (subst f1 i) (subst f2 i)

and eq_tbinder c f1 f2 = f1 == f2 ||
  let i = incr c; TTInt(!c) in
  eq_term c (subst f1 i) (subst f2 i)

and eq_term : int ref -> term -> term -> bool = fun c t1 t2 ->
  let rec eq_term t1 t2 =
    t1.elt == t2.elt ||
    match (t1.elt, t2.elt) with
    | (TCoer(t1,_)    , _              ) -> eq_term t1 t2
    | (_              , TCoer(t2,_)    ) -> eq_term t1 t2
    | (TDefi(d1)      , _              ) -> eq_term d1.value t2
    | (_              , TDefi(d2)      ) -> eq_term t1 d2.value
    | (TKAbs(f)       , _              ) -> eq_term (subst f (KProd[])) t2
    | (_              , TKAbs(f)       ) -> eq_term t1 (subst f (KProd[]))
    | (TOAbs(f)       , _              ) -> eq_term (subst f (OTInt(-1))) t2
    | (_              , TOAbs(f)       ) -> eq_term t1 (subst f (OTInt(-1)))
    | (TVari(x1)      , TVari(x2)      ) -> eq_variables x1 x2
    | (TAbst(_,f1)    , TAbst(_,f2)    )
    | (TFixY(_,f1)    , TFixY(_,f2)    ) -> eq_tbinder c f1 f2
    | (TAppl(t1,u1)   , TAppl(t2,u2)   ) -> eq_term t1 t2 && eq_term u1 u2
    | (TReco(fs1)     , TReco(fs2)     ) -> eq_assoc eq_term fs1 fs2
    | (TProj(t1,l1)   , TProj(t2,l2)   ) -> l1 = l2 && eq_term t1 t2
    | (TCons(c1,t1)   , TCons(c2,t2)   ) -> c1 = c2 && eq_term t1 t2
    | (TCase(t1,l1,d1), TCase(t2,l2,d2)) -> eq_term t1 t2 &&
                                            eq_assoc eq_term l1 l2 &&
                                            eq_option eq_term d1 d2
    | (TPrnt(s1)      , TPrnt(s2)      ) -> s1 = s2
    | (TCnst(c1)      , TCnst(c2)      ) -> eq_tcnst c c1 c2
    | (_              , _              ) -> false
  in eq_term t1 t2

and eq_tcnst c (f1,a1,b1) (f2,a2,b2) =
  eq_tbinder c f1 f2 && eq_kind c a1 a2 && eq_kind c b1 b2

and eq_ordinal : int ref -> ordinal -> ordinal -> bool = fun c o1 o2 ->
  match (orepr o1, orepr o2) with
  | (o1          , o2          ) when o1 == o2 -> true
  | (OUVar(v1)   , OUVar(v2)   ) -> eq_ouvar v1 v2
  | (OConv       , OConv       ) -> true
  | (OLess(i1,_,_), OLess(i2,_,_)) -> i1 = i2 (* && eq_ordinal c o1 o2 && eq_ord_wit c w1 w2 *)
  | (OSucc(o1)   , OSucc(o2)   ) -> eq_ordinal c o1 o2
  | (OTInt n1    , OTInt n2    ) -> n1 = n2
  | (_           , _           ) -> false

and eq_ouvar : ouvar -> ouvar -> bool = (==)

and eq_ord_wit c w1 w2 = match w1, w2 with
  | (In(t1,f1)    , In(t2,f2)    )
  | (NotIn(t1,f1) , NotIn(t2,f2) ) -> eq_term c t1 t2 && eq_obinder c f1 f2
  | (_            , _            ) -> false

let set_ouvar v o =
  assert(!v = None);
  Timed.(v := Some o)
  (* FIXME: occur check *)

let rec leq_ordinal pos c o1 o2 =
  let ptr = ref o1 in
  match (orepr o1, orepr o2) with
  | (o1         , o2         ) when eq_ordinal c o1 o2 -> true
  | (OUVar(p)   , o2         ) -> set_ouvar p o2; true
  | (o1         , OUVar(p)   ) -> set_ouvar p o1; true
  | (OSucc o1   , OSucc o2   ) -> leq_ordinal pos c o1 o2
  | (o1         , OSucc o2   ) -> leq_ordinal pos c o1 o2
  | (OSucc o1   , o2         ) when
   List.exists (fun (o1'',o1') -> ptr := o1''; eq_ordinal c o1 o1') pos
                               -> leq_ordinal pos c !ptr o2
  | (o1         , o2         ) when
   List.exists (fun (o1'',o1') -> ptr := o1''; eq_ordinal c o1 o1') pos
                               -> leq_ordinal pos c !ptr o2
  | (_          , _          ) -> false

and less_ordinal pos c o1 o2 =
  leq_ordinal pos c (OSucc o1) o2

let eq_kind : kind -> kind -> bool =
  fun k1 k2 -> Timed.pure_test (eq_kind (ref 0) k1) k2

let eq_kbinder : (kind, kind) binder -> (kind, kind) binder -> bool =
  fun f1 f2 -> Timed.pure_test (eq_kbinder (ref 0) f1) f2

let eq_term : term -> term -> bool =
  fun t1 t2 -> Timed.pure_test (eq_term (ref 0) t1) t2

let eq_ordinal : ordinal -> ordinal -> bool =
  fun t1 t2 -> Timed.pure_test (eq_ordinal (ref 0) t1) t2

let eq_ord_wit : ord_wit -> ord_wit -> bool =
  fun t1 t2 -> Timed.pure_test (eq_ord_wit (ref 0) t1) t2

let leq_ordinal : (ordinal * ordinal) list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (leq_ordinal pos (ref 0) t1) t2

let less_ordinal : (ordinal * ordinal) list -> ordinal -> ordinal -> bool =
  fun pos t1 t2 -> Timed.pure_test (less_ordinal pos (ref 0) t1) t2
