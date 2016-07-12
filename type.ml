open Ast
open Compare
open Position
open Bindlib
open Format

let rec assoc_ordinal o = function
  | [] -> raise Not_found
  | (o',v)::l -> if eq_ordinal o o' then v else assoc_ordinal o l

(* construction of an ordinal < o such that w *)

let oless o w =
  let o = orepr o in
  match o with
  | OSucc o' -> o'
  | OUVar(p) ->
    let o' = OUVar(ref None) in
    set_ouvar p (OSucc o'); o'
  | _ ->
  OLess(o,w)

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
    | TFixY(n,f)  -> tfixy t.pos n (in_pos t.pos (binder_name f))
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
 *****************************************************************)
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
    | TPrnt _     -> false
    | TTInt _     -> assert false
  in fn t

(*****************************************************************
 *              test if a term is neutral in CBV                 *
 *****************************************************************)
let is_neutral : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> fn t
    | TVari(x)    -> true
    | TAbst(ko,f) -> false
    | TFixY(ko,f) -> false
    | TKAbs(f)    -> fn (subst f (KProd []))
    | TOAbs(f)    -> fn (subst f (OConv))
    | TAppl(a,b)  -> fn a
    | TReco(fs)   -> false
    | TProj(a,s)  -> fn a
    | TCons(s,a)  -> false
    | TCase(a,fs) -> fn a
    | TDefi(d)    -> true
    | TCnst _     -> true
    | TPrnt _     -> false
    | TTInt _     -> assert false
  in fn t


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
    | MuRec(_,k)
    | NuRec(_,k) -> aux occ acc k)
  and aux2 acc t =
    if List.memq t !adone_t then acc else (
    adone_t := t :: !adone_t;
    match t.elt with
    | TCnst(t,k1,k2) -> aux2 (aux Eps (aux Eps acc k1) k2) (subst t (dummy_pos (TReco [])))
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
      | MuRec(_,k)
      | NuRec(_,k) -> fn k
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
      | MuRec(_,k)
      | NuRec(_,k)   -> fn k
      | k            -> box k
    and gn o =
      match orepr o with
      | OVari(x) -> box_of_var x
      | OSucc(o) -> osucc (gn o)
      | OUVar(u) -> if eq_ouvar v u then x else box (OUVar(u))
      | o        -> box o
    in fn k))

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
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | MuRec _
      | NuRec _    -> assert false
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
      | MuRec(_,k)
      | NuRec(_,k) -> fn k
      | t          -> box t
    and gn o =
      match orepr o with
      | OSucc o -> osucc (gn o)
      | OVari x -> box_of_var x
      | OUVar(ov) -> if ov == ov0 then x else box o
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

let decompose : occur -> kind -> kind ->
                  kind * kind * (int * ordinal) list = fun pos k1 k2 ->
  let res = ref [] in
  let i = ref 0 in
  let rec search pos o =
    let o = orepr o in
    match o with
    | OLess _ when pos <> Eps->
       (try
          box (OTInt(assoc_ordinal o !res))
        with
          Not_found ->
            let n = !i in incr i; res := (o, n) :: !res; box (OTInt n))
    | OSucc o -> osucc(search pos o)
    | OVari o -> box_of_var o
    | _ -> box o
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
    | KFixM(o,f) ->
       kfixm (binder_name f) (search pos o) (fun x -> fn pos (subst f (KVari x)))
    | KFixN(o,f) ->
       kfixn (binder_name f) (search pos o) (fun x -> fn pos (subst f (KVari x)))
    | KDefi(d,o,a) ->
       kdefi d
         (Array.mapi (fun i -> search (compose pos d.tdef_ovariance.(i))) o)
         (Array.mapi (fun i -> fn (compose pos d.tdef_kvariance.(i))) a)
    | KDPrj(t,s) -> kdprj (map_term (fn Eps) t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn pos t) s (fn Eps a)
    | KVari(x)   -> box_of_var x
    | MuRec(_,k)
    | NuRec(_,k) -> fn pos k
    | t          -> box t
  in
  let k1 = unbox (fn (neg pos) k1) in
  let k2 = unbox (fn pos k2) in
  (k1, k2, List.rev_map (fun (o,n) -> (n,o)) !res)

let recompose : kind -> (int * ordinal) list -> kind = fun k os ->
  let rec get o = match orepr o with
      | OTInt i -> (try box (List.assoc i os) with Not_found -> assert false)
      | OSucc o -> osucc (get o)
      | OVari v -> box_of_var v
      | o -> box o
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
    | KFixM(o, f) -> kfixm (binder_name f) (get o) (fun x -> fn (subst f (KVari x)))
    | KFixN(o, f) -> kfixn (binder_name f) (get o) (fun x -> fn (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KDefi(d,o,a) -> kdefi d (Array.map get o) (Array.map fn a)
    | KDPrj(t,s) -> kdprj (map_term fn t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
    | MuRec _
    | NuRec _    -> assert false
    | t          -> box t
  in
  unbox (fn k)
