open Ast
open Compare
open Position
open Bindlib
open Format
open Term

let rec assoc_ordinal o = function
  | [] -> raise Not_found
  | (o',v)::l -> if strict_eq_ordinal o o' then v else assoc_ordinal o l

(* construction of an ordinal < o such that w *)

let opred o w =
  let o = orepr o in
  match o with
  | OSucc o' -> o'
  | OUVar(p,None) ->
    let o' = OUVar(ref None, None) in
    set_ouvar p (OSucc o'); o'
  | _ -> OLess(o, w)


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

let compose2 oa ob =
  match oa with
  | Reg(i,a) -> a.(i) <- combine a.(i) ob; Non
  | _        -> compose oa ob

let neg = function
  | Reg(_) -> assert false
  | Neg    -> Pos
  | Pos    -> Neg
  | o      -> o

(* FIXME: should memoize this function, because a lot of sub-term are shared
   and we traverse all constants ... One could also precompute the
   variance of definitions to avoid substitution *)
let kuvar_occur : kuvar -> kind -> occur = fun {kuvar_key = i} k ->
  let kdummy = KProd [] in
  let odummy = OTInt(-42) in
  let adone_k = ref [] in
  let adone_t = ref [] in
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
    | KUVar(u)   -> if u.kuvar_key = i then combine acc occ else acc
    | KTInt(_)   -> assert false
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
    | TOAbs(f)       -> aux2 acc (subst f (OTInt(-1)))
    | TAppl(t1, t2)  -> aux2 (aux2 acc t1) t2
    | TReco(l)       -> List.fold_left (fun acc (_,t) -> aux2 acc t) acc l
    | TCase(t,l,d)   ->
       let acc = match d with None -> acc | Some t -> aux2 acc t in
       List.fold_left (fun acc (_,t) -> aux2 acc t) (aux2 acc t) l
    | TVari(_)
    | TDefi(_)
    | TPrnt(_)
    | TTInt(_)       -> acc)
  and aux3 acc = function
    | OLess(o,(In(t,f)|NotIn(t,f))) -> aux Eps (aux2 (aux3 acc o) t) (subst f odummy)
    | OSucc o -> aux3 acc o
    (* we keep this to ensure valid proof when simplifying useless induction
       needed because has_uvar below does no check ordinals *)
    | _             -> acc
  in aux Pos Non k

(****************************************************************************
 *                 Binding a unification variable in a type                 *
 ****************************************************************************)

let bind_kuvar : kuvar -> kind -> (kind, kind) binder = fun v k ->
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
      | KUVar(u)   -> assert(!(u.kuvar_val) = None); if eq_kuvar v u then x else box k
      | KVari(x)   -> box_of_var x
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | KMRec(_,k)
      | KNRec(_,k) -> fn k
      | t          -> box t
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | OSucc o -> osucc (gn o)
      | o -> box o
    in
    fn k))

let set_kuvar side v k =
  assert (!(v.kuvar_val) = None);
  let k =
    match !(v.kuvar_state) with
    | Free -> k
    | Sum l -> KDSum(l)
    | Prod l -> KProd(l)
  in
  let k =
    match kuvar_occur v k with
    | Non -> k
    | Pos -> KFixM(OConv,bind_kuvar v k)
    | _   -> if side then bot else top
  in
  Io.log_uni "set %a <- %a\n\n%!"
    (!fprint_kind false) (KUVar v) (!fprint_kind false) k;
  Timed.(v.kuvar_val := Some k)

let bind_ouvar : ouvar -> kind -> (ordinal, kind) binder = fun v k ->
  unbox (bind mk_free_ovari "α" (fun x ->
    let rec fn k =
      match repr k with
      | KFunc(a,b)   -> kfunc (fn a) (fn b)
      | KProd(fs)    -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
      | KDSum(cs)    -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
      | KKAll(f)     -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KKExi(f)     -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
      | KOAll(f)     -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KOExi(f)     -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
      | KFixM(o,f)   -> kfixm (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KFixN(o,f)   -> kfixn (binder_name f) (gn o) (fun x -> fn (subst f (KVari x)))
      | KVari(x)     -> box_of_var x
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KDPrj(t,s)   -> kdprj (map_term fn t) s
      | KWith(t,c)   -> let (s,a) = c in kwith (fn t) s (fn a)
      | KMRec(_,k)
      | KNRec(_,k)   -> fn k
      | k            -> box k
    and gn o =
      match orepr o with
      | OVari(x) -> box_of_var x
      | OSucc(o) -> osucc (gn o)
      | OUVar(u,o') -> if eq_ouvar v u then x else box (OUVar(u,o')) (* FIXME *)
      | o        -> box o
    in fn k))

(****************************************************************************
 *                            lifting of kind                               *
****************************************************************************)

let rec lift_kind : kind -> kind bindbox = fun k ->
  match repr k with
  | KFunc(a,b) -> kfunc (lift_kind a) (lift_kind b)
  | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, lift_kind a)) fs)
  | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, lift_kind a)) cs)
  | KKAll(f)   -> kkall (binder_name f) (fun x -> lift_kind (subst f (KVari x)))
  | KKExi(f)   -> kkexi (binder_name f) (fun x -> lift_kind (subst f (KVari x)))
  | KOAll(f)   -> koall (binder_name f) (fun x -> lift_kind (subst f (OVari x)))
  | KOExi(f)   -> koexi (binder_name f) (fun x -> lift_kind (subst f (OVari x)))
  | KFixM(o,f) ->
     kfixm (binder_name f) (lift_ordinal o)
       (fun x -> lift_kind (subst f (KVari x)))
  | KFixN(o,f) ->
     kfixn (binder_name f) (lift_ordinal o)
       (fun x -> lift_kind (subst f (KVari x)))
  | KVari(x)   -> box_of_var x
  | KDefi(d,o,a) -> kdefi d (Array.map lift_ordinal o) (Array.map lift_kind a)
  | KDPrj(t,s) -> kdprj (map_term lift_kind t) s
  | KWith(t,c) -> let (s,a) = c in kwith (lift_kind t) s (lift_kind a)
  | KMRec _
  | KNRec _    -> assert false
  | t          -> box t
and lift_ordinal : ordinal -> ordinal bindbox = fun o ->
  match orepr o with
  | OVari x -> box_of_var x
  | OSucc o -> osucc (lift_ordinal o)
  | OLess _  -> assert false (* do not support binding trhough witness even if this
                                is possible in principle *)
  | OConv | OUVar _ | OTInt _ -> box o

let lift_term = map_term lift_kind

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
      | KUVar(u)   -> assert(!(u.kuvar_val) = None); box k
      | KVari(x)   -> box_of_var x
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | KMRec(_,k)
      | KNRec(_,k) -> fn k
      | t          -> box t
    and gn o =
      match orepr o with
      | OSucc o -> osucc (gn o)
      | OVari x -> box_of_var x
      | OUVar(ov, _) -> if ov == ov0 then x else box o (* FIXME *)
      | o -> box o
    in
    fn k))

(****************************************************************************
 *                Closedness tests for terms, kind and ordinals             *
 ****************************************************************************)

let rec has_boundvar k =
  let k = repr k in
  match k with
  | KFunc(a,b) -> has_boundvar a; has_boundvar b
  | KProd(ls)
  | KDSum(ls)  -> List.iter (fun (l,a) -> has_boundvar a) ls
  | KKAll(f)
  | KKExi(f)   -> has_boundvar (subst f (KProd []))
  | KFixM(o,f)
  | KFixN(o,f) -> has_oboundvar o; has_boundvar (subst f (KProd []))
  | KOAll(f)
  | KOExi(f)   -> has_boundvar (subst f (OTInt 0))
  | KDefi(d,o,a) -> Array.iter has_oboundvar o; Array.iter has_boundvar a
  | KWith(k,c) -> let (_,b) = c in has_boundvar k; has_boundvar b
  | KDPrj(t,s) -> has_tboundvar t
  | KMRec(o,k) -> has_boundvar k (* In the current version, no bound ordinal in o *)
  | KNRec(o,k) -> has_boundvar k (* In the current version, no bound ordinal in o *)
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
  | KVari _ -> raise Exit
  | KUCst _ | KECst _ | KUVar _ | KTInt _ -> ()

and has_tboundvar t =
  match t.elt with
  | TCoer(t,k) -> has_tboundvar t; has_boundvar k
  | TVari _ -> raise Exit
  | TAbst(ko, b) ->
     has_tboundvar (subst b (TTInt 0));
     (match ko with None -> () | Some k -> has_boundvar k)
  | TAppl(t1,t2) -> has_tboundvar t1; has_tboundvar t2;
  | TReco(l) -> List.iter (fun (_,t) -> has_tboundvar t) l
  | TProj(t,s) -> has_tboundvar t
  | TCons(s,t) -> has_tboundvar t
  | TCase(t,l,ao) -> has_tboundvar t; List.iter (fun (_,t) ->  has_tboundvar t) l;
    (match ao with None -> () | Some t -> has_tboundvar t)
  | TFixY(_,_,b) -> has_tboundvar (subst b (TTInt 0))
  | TKAbs(b) -> has_tboundvar (subst b (KTInt 0))
  | TOAbs(b) -> has_tboundvar (subst b (OTInt 0))
  | TDefi _ | TPrnt _ | TTInt _ | TCnst _ -> ()

and has_oboundvar o =
  let o = orepr o in
    match o with
    | OVari _ -> raise Exit
    | OSucc o -> has_oboundvar o
    | OLess(o,w) ->
       (match wrepr w with
       | In(t,b) | NotIn(t,b) ->
          has_oboundvar o; has_tboundvar t; has_boundvar (subst b OConv)
       |  WUVar _ -> ())
    | OTInt _ | OUVar _ | OConv -> ()

let closed_term t = try has_tboundvar t; true with Exit -> false
let closed_kind k = try has_boundvar k; true with Exit -> false
let closed_ordinal o = try has_oboundvar o; true with Exit -> false

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

(* This function index all the ordinal in two kinds,
   select the usefull par of the context and return
   the usefull relations between two ordinals *)
let decompose : ordinal list -> kind -> kind ->
    ordinal list * kind * kind * (int * ordinal) list * (ordinal * ordinal) list = fun pos k1 k2 ->
  let res = ref [] in
  let i = ref 0 in
  let rec search o =
    let o = orepr o in
    match o with
    | OLess(_,_) ->
       assert (closed_ordinal o);
       (try
          box (OTInt(assoc_ordinal o !res))
        with
          Not_found ->
            let n = !i in incr i; res := (o, n) :: !res;
            box (OTInt n))
    | OSucc o -> osucc(search o)
    | OVari o -> box_of_var o
    | OUVar _ | OConv -> box o
    | OTInt _ -> assert false
  and fn k =
    match repr k with
    | KFunc(a,b) -> kfunc (fn a) (fn b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn (subst f (OVari x)))
    | KFixM(OConv,f) when !contract_mu && is_mu f ->
       let aux x =
         match full_repr (subst f x) with
         | KFixM(OConv,g) -> subst g x
         | _              -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = KFixM(OConv, f) in
       fn a'
    | KFixN(OConv,f) when !contract_mu && is_nu f ->
       let aux x =
         match full_repr (subst f x) with
         | KFixN(OConv,g) -> subst g x
         | _              -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) aux in
       let a' = KFixN(OConv, f) in
       fn a'
    | KFixM(o,f) ->
       kfixm (binder_name f) (search o) (fun x -> fn (subst f (KVari x)))
    | KFixN(o,f) ->
       kfixn (binder_name f) (search o) (fun x -> fn (subst f (KVari x)))
    | KDefi(d,o,a) -> kdefi d (Array.map search o) (Array.map fn a)
    | KDPrj(t,s) -> kdprj (map_term fn t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
    | KVari(x)   -> box_of_var x
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | t          -> box t
  in
  let k1 = unbox (fn k1) in
  let k2 = unbox (fn k2) in
  (* we build the relation graph, which includes positive ordinals not
     in the judgement iff the are between to such ordinals *)
  let relation = ref [] in
  let rec fn acc o0 o =
    if List.exists (fun (o1, _) -> strict_eq_ordinal o o1) !relation then ()
    else match orepr o with
    | OLess(o1,_)   | OUVar(_, Some o1) ->
       (try
         let _ = assoc_ordinal o1 !res in
         relation := (o0,o1) :: acc @ !relation;
         fn [] o1 o1
        with Not_found ->
          fn ((o0,o1) :: acc) o1 o1)
    | _ -> ()

  in
  List.iter (fun (o2,_) -> fn [] o2 o2) !res;
  let relation = List.map (fun (o1,o2) -> unbox (search o1), unbox (search o2)) !relation in
  (* select the usefull part of the context *)
  let pos = List.filter (fun o1 ->
    List.exists (fun (o2,_) -> strict_eq_ordinal o1 o2) !res) pos in
  let pos = List.map (fun o ->
    try OTInt(assoc_ordinal o !res) with Not_found -> assert false) pos in
  let pos = List.sort compare pos in
  (pos, k1, k2, List.rev_map (fun (o,n) -> (n,o)) !res, relation)


let recompose : ordinal list-> kind -> (int * ordinal) list -> (ordinal * ordinal) list ->
    (int * ordinal) list * ordinal list * kind
  =
  let rec get os o = match orepr o with
      | OTInt i -> (try box (List.assoc i os) with Not_found -> assert false)
      | OSucc o -> osucc (get os o)
      | OVari v -> box_of_var v
      | o -> box o
  in
  let rec fn os k =
    match repr k with
    | KFunc(a,b) -> kfunc (fn os a) (fn os b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn os a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn os a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn os (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn os (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn os (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn os (subst f (OVari x)))
    | KFixM(o, f) -> kfixm (binder_name f) (get os o) (fun x -> fn os (subst f (KVari x)))
    | KFixN(o, f) -> kfixn (binder_name f) (get os o) (fun x -> fn os (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KDefi(d,o,a) -> kdefi d (Array.map (get os) o) (Array.map (fn os) a)
    | KDPrj(t,s) -> kdprj (map_term (fn os) t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn os t) s (fn os a)
    | KMRec _
    | KNRec _    -> assert false
    | t          -> box t
  in
  fun pos k os rel ->
    let res = ref [] in
    let rec search o =
      match o with
      | OTInt i ->
         (try
           List.assoc i !res
         with Not_found ->
           let o =
             try
               let o' = assoc_ordinal (OTInt i) rel in
               OLess(search o', WUVar(ref None))
             with
               Not_found -> OUVar(ref None, None)
           in
           res := (i, o) :: !res;
           o)
      | o -> Io.err "==> %a\n%!" (!fprint_ordinal false) o; assert false
    in
    List.iter (fun (i,_) -> ignore (search (OTInt i))) os;
    assert (List.length !res = List.length os);
    let os = !res in
    os, List.map (fun o1 -> unbox (get os o1)) pos, unbox (fn os k)

(* Matching kind, used for printing only *)

let rec match_kind : kind -> kind -> bool = fun p k ->
  match full_repr p, full_repr k with
  | KUVar(ua), k -> set_kuvar true ua k; true
  | KFunc(p1,p2), KFunc(k1,k2) -> match_kind p1 k1 && match_kind p2 k2
  | KDSum(ps1), KDSum(ps2)
  | KProd(ps1), KProd(ps2) ->
     List.length ps1 = List.length ps2 &&
     let ps1 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps1 in
     let ps2 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps2 in
     List.for_all2 (fun (s1,p1) (s2,k1) ->
       s1 = s2 && match_kind p1 k1) ps1 ps2
  | KDPrj(t1,s1), KDPrj(t2,s2) ->
     s1 = s2 && strict_eq_term t1 t2
  | KWith(p1,(s1,p2)), KWith(k1,(s2,k2)) ->
     s1 = s2 && match_kind p1 k1 && match_kind p2 k2
  | KKAll(f), KKAll(g)
  | KKExi(f), KKExi(g) ->
     let v = new_kvari (binder_name f) in
     match_kind (subst f (free_of v)) (subst g (free_of v))
  | KOAll(f), KOAll(g)
  | KOExi(f), KOExi(g) ->
     let v = new_ovari (binder_name f) in
     match_kind (subst f (free_of v)) (subst g (free_of v))
  | KFixM(o1,f), KFixM(o2,g)
  | KFixN(o1,f), KFixN(o2,g) ->
     let v = new_kvari (binder_name f) in
     match_ordinal o1 o2 &&
       match_kind (subst f (free_of v)) (subst g (free_of v))
  | KVari(v1), KVari(v2) -> compare_variables v1 v2 = 0
  | p, k -> strict_eq_kind p k

and match_ordinal : ordinal -> ordinal -> bool = fun p o ->
  match orepr p, orepr o with
  | OUVar(uo,_), o when not (occur_ouvar uo o) -> set_ouvar uo o; true (* FIXME, but printing only *)
  | OSucc(p), OSucc(o) -> match_ordinal p o
  | p, k -> strict_eq_ordinal p k
