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
  | OUVar({ouvar_bnd = None} as p) ->
    let o' = new_ouvar () in
    set_ouvar p (OSucc o'); o'
  | _ -> OLess(o, w)

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
      | KUVar(u,_) -> assert(!(u.kuvar_val) = None); if eq_kuvar v u then x else box k
                      (* TODO: is it ok to ignore ordinal parameters *)
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

let mbind_assoc cst size l =
  unbox (mbind mk_free_ovari (Array.make size "_")
           (fun v -> cst (List.map (fun (s,k) -> (s, mbind_apply (box k) (box_array v))) l)))

let set_kuvar left_side v k os =
  assert (!(v.kuvar_val) = None);
  let k =
    match !(v.kuvar_state) with
    | Free -> k
    | Sum l -> mbind_assoc kdsum v.kuvar_arity l
    (* TODO: on jette K ... normal mais bof*)
    | Prod l -> mbind_assoc kprod v.kuvar_arity l
  in
  assert (mbinder_arity k = v.kuvar_arity);
  let osl = Array.to_list os in
  let k =
    match kuvar_occur ~safe_ordinals:osl v (msubst k (Array.make v.kuvar_arity OConv)) with
    | Non -> k
    | Pos -> unbox (mbind mk_free_ovari (Array.make v.kuvar_arity "_") (fun x ->
      box (KFixM(OConv,bind_kuvar v (msubst k (Array.make v.kuvar_arity OConv))))))
    | _   ->
       if left_side then
         unbox (mbind mk_free_ovari (Array.make v.kuvar_arity "_") (fun x -> box bot))
       else
         unbox (mbind mk_free_ovari (Array.make v.kuvar_arity "_") (fun x -> box top))
  in
  Io.log_uni "set %a <- %a\n\n%!"
    (!fprint_kind false) (KUVar(v,os)) (!fprint_kind false)
    (msubst k (Array.init v.kuvar_arity (fun i -> free_of (new_ovari ("a_"^string_of_int i))))) ;
  Timed.(v.kuvar_val := Some k)

let _ = fset_kuvar := set_kuvar

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
      | OUVar(u) -> if eq_ouvar v u then x else box o (* FIXME *)
      | o        -> box o
    in fn k))

let bind_ordinals : ordinal array -> kind -> (ordinal, kind) mbinder = fun os k ->
  let len = Array.length os in
  Io.log_sub "bind ordinals %d\n%!" len;
  let res = unbox (mbind mk_free_ovari (Array.make len "α") (fun x ->
    let index u =
      let rec fn i =
        if i >= len then raise Not_found else (
          if strict_eq_ordinal os.(i) u then x.(i) else
            fn (i+1))
      in
      fn 0
    in
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
      let o = orepr o in
      try
        index o
      with
        Not_found ->
          match orepr o with
          | OVari(x) -> box_of_var x
          | OSucc(o) -> osucc (gn o)
          | o        -> box o
    in fn k))
  in
  Io.log_sub "bind ordinals fin %d\n%!" (mbinder_arity res);
  res

let _ = fbind_ordinals := bind_ordinals

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
  | OConv | OUVar _ -> box o

let lift_term = map_term lift_kind

(****************************************************************************
 *                 Binding a unification variable in a type                 *
 ****************************************************************************)

let bind_ovar : ouvar-> kind -> (ordinal, kind) binder = fun ov0 k ->
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
      | KUVar(u,os)-> assert(!(u.kuvar_val) = None); box k
      | KVari(x)   -> box_of_var x
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KDPrj(t,s) -> kdprj (map_term fn t) s
      | KWith(t,c) -> let (s,a) = c in kwith (fn t) s (fn a)
      | KMRec(_,k)
      | KNRec(_,k) -> fn k
      | t          -> box t
    and gn o =
      match orepr o with
      | OSucc o  -> osucc (gn o)
      | OVari x  -> box_of_var x
      | OUVar(v) -> if eq_ouvar v ov0 then x else box o (* FIXME *)
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
  | KOExi(f)   -> has_boundvar (subst f OConv)
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
  | TOAbs(b) -> has_tboundvar (subst b OConv)
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
       | Gen(t,r,f) ->
          let os = Array.make (mbinder_arity f) OConv in
          let (k1,k2) = msubst f os in
          has_boundvar k1; has_boundvar k2
       | Link _ -> ())
    | OUVar _ | OConv -> ()

let closed_term t = try has_tboundvar t; true with Exit -> false
let closed_kind k = try has_boundvar k; true with Exit -> false
let closed_ordinal o = try has_oboundvar o; true with Exit -> false

(****************************************************************************
 *                    Decomposition type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

exception BadDecompose

(* This function index all the ordinal in two kinds,
   select the usefull par of the context and return
   the usefull relations between two ordinals *)
let decompose : ordinal list -> kind -> kind ->
  int list * (int * int) list * (ordinal, kind * kind) mbinder * (int * ordinal) list = fun pos k1 k2 ->
  let res = ref [] in
  let i = ref 0 in
  let relation = ref [] in
  let delayed = ref [] in
  let initial = ref true in
  let new_uvar = ref [] in
  let register f =
    if !initial then
      delayed := f :: !delayed
    else
      f ()
  in
  (* FIXME: with delayed, keep could be removed,
     because ordinal in the formula are always firsts *)
  let rec eps_search keep o =
    assert (closed_ordinal o);
    match o with
    | OLess(o',w) ->
       assert (closed_ordinal o);
       (try
          let (n,v,k) = assoc_ordinal o !res in
          k := !k || keep;
          (n,v)
        with
          Not_found ->
            let n = !i in incr i;
            let v = new_ovari ("o_" ^ string_of_int n) in
            res := (o, (n, v, ref keep)) :: !res;
            if o' <> OConv then (
              register (fun () ->
                (* delayed to have order depending upon the formula only *)
                let (p, _) = eps_search false o' in
                relation := (n,p)::!relation));
            (n, v))
    | o -> raise BadDecompose
  and search pos o =
    let o = orepr o in
    match o with
    | OLess _ -> let (_, v) = eps_search true o in box_of_var v
    | OSucc o -> osucc(search pos o)
    | OVari o -> box_of_var o
    | OUVar _ -> raise BadDecompose
    | OConv when pos = Pos ->
       let n = !i in incr i;
       let v = new_ovari ("o_" ^ string_of_int n) in
       res := (OConv, (n, v, ref true)) :: !res; box_of_var v
    | OConv   -> box OConv
  and fn pos k =
    match full_repr k with
    | KFunc(a,b) -> kfunc (fn (neg pos) a) (fn pos b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KFixM(o,f) ->
       kfixm (binder_name f) (search (neg pos) o) (fun x -> fn pos (subst f (KVari x)))
    | KFixN(o,f) ->
       kfixn (binder_name f) (search pos o) (fun x -> fn pos (subst f (KVari x)))
    | KDPrj(t,s) -> kdprj (map_term (fn Eps) t) s
    | KWith(t,c) -> let (s,a) = c in kwith (fn Eps t) s (fn pos a)
    | KVari(x)   -> box_of_var x
    | KMRec(_,k)
    | KNRec(_,k) -> fn pos k
    | KUVar(v,os) when not !initial && not (List.memq v !new_uvar) ->
       let os',os'' = List.fold_left (fun (acc1, acc2 as acc) (o,(n,w,k)) ->
         if not (kuvar_ord_occur v o) &&
           not (List.exists (strict_eq_ordinal o) acc1)
         then (o::acc1, (box_of_var w)::acc2) else acc) ([], []) !res in
       let os' = Array.of_list os' in
       let os'' = Array.of_list os'' in
       let old_len = Array.length os in
       let new_len = Array.length os' + old_len in
       if new_len <= old_len then
         box_apply (fun os -> KUVar(v, os)) (box_array (Array.map (search Eps) os))
       else
         (* FIXME: manage the state, break lib/stream.typ *)
         let u = new_kuvara new_len in
         new_uvar := u :: !new_uvar;
         let k = unbox (mbind mk_free_ovari (Array.make old_len "_") (fun x ->
           box_apply (fun os -> KUVar(u,os))
             (box_array (Array.init new_len (fun i ->
               if i < old_len then x.(i) else box os'.(i - old_len))))))
         in
         assert(!(v.kuvar_val) = None);
         set_kuvar (pos = Neg) v k os;
         box_apply (fun os -> KUVar(u, os))
           (box_array (Array.append (Array.map (search Eps) os) os''))
    | KUVar(v,os) ->
       box_apply (fun os -> KUVar(v, os))
           (box_array (Array.map (search Eps) os))
    | t          -> box t (* FIXME: Témoin de type à traverser *)
  in
  let _ = fn Neg k1 in
  let _ = fn Pos k2 in

  initial := false;

  List.iter (fun f -> f()) !delayed;
  let pos = List.map (fun o -> fst (eps_search false o)) pos in

  let k1 = fn Neg k1 in
  let k2 = fn Pos k2 in

  let both = box_pair k1 k2 in

  let res = List.filter (fun (o,(n,v,k)) -> !k) !res in
  let ovars = Array.of_list (List.map (fun (o,(n,v,_)) -> v) res) in
  let both = unbox (bind_mvar ovars both) in

  let tbl = List.mapi (fun i (o,(n,v,k)) -> (n,i)) res in
  let os = List.map (fun (o,(n,v,_)) -> (List.assoc n tbl, o)) res in

  let rec next start n =
    if List.exists (fun (q,_) -> n = q) tbl then ((*if not start then Io.log "SKIP\n%!";*) n) else
      try
        assert (List.length (List.find_all (fun (n',_) -> n = n') !relation) <= 1);
        let n = List.assoc n !relation in
        next false n
      with Not_found -> n
  in

  let pos = List.map (next true) pos in
  let pos = List.sort_uniq (-) pos in
  let pos = List.filter (fun n -> List.exists (fun (q,_) -> n = q) tbl) pos in
  let pos = List.map (fun n -> List.assoc n tbl) pos in

  let rel = List.map (fun (n,p) -> (n, next true p)) !relation in
  let rel = List.filter (fun (n,p) ->
    List.exists (fun (q,_) -> n = q) tbl && List.exists (fun (q,_) -> p = q) tbl) rel in
  let rel = List.map (fun (n,p) -> List.assoc n tbl, List.assoc p tbl) rel in
(*
  Io.log_sub "decompose pos: %a\n%!" (fun ff l -> List.iter (Format.fprintf ff "%d ") l) pos;
  Io.log_sub "decompose rel: %a\n%!" (fun ff l -> List.iter (fun (a,b) -> Format.fprintf ff "(%d,%d) "a b) l) rel;
  Io.log_sub "decompose os : %a\n%!" (fun ff l -> List.iter (fun (n,o) -> Format.fprintf ff "(%d,%a) "n (!fprint_ordinal false) o) l) os;*)

  assert(mbinder_arity both = List.length os);
  (pos, rel, both, os)

exception BadRecompose

let recompose : int list -> (int * int) list -> (ordinal, kind * kind) mbinder -> bool ->
    (int * ordinal) list * ordinal list * kind * kind
  =
  fun pos rel both general ->
    let res = ref [] in
    let forbidden = ref [] in
    let arity = mbinder_arity both in
    let rec search i =
      assert (i < arity && not (List.mem i !forbidden));
      try
        List.assoc i !res
      with Not_found ->
        forbidden := i::!forbidden;
        let o =
          if general then
            try
            (*OLess(search (List.assoc i rel), Link (ref None))*)
              new_ouvar ~bound:(search (List.assoc i rel)) ()
            with Not_found ->
              new_ouvar ()
          else
             let o' = try search (List.assoc i rel) with Not_found -> OConv in
             OLess(o',Gen(i,rel,both))
        in
        res := (i, o) :: !res;
        forbidden := List.tl !forbidden;
        o
    in
    let ovars = Array.init arity search in
    let (k1, k2) = msubst both ovars in
    let pos = List.map (fun i -> assert (i < arity); ovars.(i)) pos in
    let os = Array.to_list (Array.mapi (fun i x -> (i,x)) ovars) in
    (*    Io.log_sub "recompose os : %a\n%!" (fun ff l -> List.iter (fun (n,o) -> Format.fprintf ff "(%d,%a) "n (!fprint_ordinal false) o) l) os;*)
    os, pos, k1, k2

(* Matching kind, used for printing only *)

let rec match_kind : kuvar list -> ouvar list -> kind -> kind -> bool = fun kuvars ouvars p k ->
  let res = match full_repr p, full_repr k with
  | KUVar(ua,[||]), k when List.memq ua kuvars ->
     set_kuvar true ua (unbox (mbind mk_free_ovari [||] (fun _ -> box k))) [||];
     true
  | KFunc(p1,p2), KFunc(k1,k2) -> match_kind kuvars ouvars p1 k1 && match_kind kuvars ouvars p2 k2
  | KDSum(ps1), KDSum(ps2)
  | KProd(ps1), KProd(ps2) ->
     List.length ps1 = List.length ps2 &&
     let ps1 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps1 in
     let ps2 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps2 in
     List.for_all2 (fun (s1,p1) (s2,k1) ->
       s1 = s2 && match_kind kuvars ouvars p1 k1) ps1 ps2
  | KDPrj(t1,s1), KDPrj(t2,s2) ->
     s1 = s2 && strict_eq_term t1 t2
  | KWith(p1,(s1,p2)), KWith(k1,(s2,k2)) ->
     s1 = s2 && match_kind kuvars ouvars p1 k1 && match_kind kuvars ouvars p2 k2
  | KKAll(f), KKAll(g)
  | KKExi(f), KKExi(g) ->
     let v = new_kvari (binder_name f) in
     match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KOAll(f), KOAll(g)
  | KOExi(f), KOExi(g) ->
     let v = new_ovari (binder_name f) in
     match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KFixM(o1,f), KFixM(o2,g)
  | KFixN(o1,f), KFixN(o2,g) ->
     let v = new_kvari (binder_name f) in
     match_ordinal ouvars o1 o2 &&
       match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KVari(v1), KVari(v2) -> compare_variables v1 v2 = 0
  | p, k -> strict_eq_kind p k
  in
  res

and match_ordinal : ouvar list -> ordinal -> ordinal -> bool = fun ouvars p o ->
  let res = match orepr p, orepr o with
  | OUVar(uo), o when List.memq uo ouvars -> set_ouvar uo o; true
  | OSucc(p), OSucc(o) -> match_ordinal ouvars p o
  | p, k -> strict_eq_ordinal p k in
  res
