open Ast
open Compare
open Position
open Bindlib
open Format
open Term

(* construction of an ordinal < o such that w *)

let rec opred o w =
  let o = orepr o in
  match o with
  | OSucc o' -> o'
  | OUVar({uvar_state = (None,None); uvar_arity = a} as p, os) ->
     let o' = OUVar(new_ouvara a,os) in
     set_ouvar p (!fobind_ordinals os (OSucc o')); o'
  | OUVar({uvar_state = (Some o',None); uvar_arity = a} as p, os) ->
     set_ouvar p o'; opred o w
  | _ -> OLess(o, w)

exception Occur_check

(****************************************************************************
*                      lifting of kind and ordinals                         *
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
  | KMRec _
  | KNRec _    -> assert false
  | KUVar(u,os)-> kuvar u (Array.map lift_ordinal os)
  | KUCst(t,f,cl) ->
     if cl then box k else
       kucst (binder_name f) (lift_term t) (fun x -> lift_kind (subst f (KVari x)))
  | KECst(t,f,cl) ->
     if cl then box k else
       kecst (binder_name f) (lift_term t) (fun x -> lift_kind (subst f (KVari x)))

and lift_ordinal : ordinal -> ordinal bindbox = fun o ->
  match orepr o with
  | OVari x -> box_of_var x
  | OSucc o -> osucc (lift_ordinal o)
  | OLess(o,In(t,w))  -> oless_In (lift_ordinal o) (lift_term t)
     (vbind mk_free_ovari (binder_name w) (fun x -> lift_kind (subst w (OVari x))))
  | OLess(o,NotIn(t,w))  -> oless_NotIn (lift_ordinal o) (lift_term t)
     (vbind mk_free_ovari (binder_name w) (fun x -> lift_kind (subst w (OVari x))))
  | OLess(o,Gen(i,r,p))  ->
     oless_Gen (lift_ordinal o) i r
       (mvbind mk_free_ovari (mbinder_names p) (fun xs ->
         let k1, k2 = msubst p (Array.map (fun x -> OVari x) xs) in box_pair (lift_kind k1) (lift_kind k2)))
  | OUVar(u,os) -> ouvar u (Array.map lift_ordinal os)
  | OConv -> box o

and lift_term t = map_term lift_kind t

(****************************************************************************
 *                    Increase ordinals in covariant position               *
 *                      that cannot be used by the variable u               *
 *                       to allow setting the value of an uvar              *
 ****************************************************************************)

(* FIXME: pos is the polarity of the variable u, not k , this is not natural, should be inversed *)
let make_safe pos u k =
  let rec gn o = match orepr o with
    | o when not (kuvar_ord_occur u o) -> lift_ordinal o
    | OLess(o',_) -> gn o'
    | o -> lift_ordinal o
  in
  let kn pos o =
    if pos = Pos then gn o else lift_ordinal o
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
    | KFixM(o,f) ->
       kfixm (binder_name f) (kn pos o) (fun x -> fn pos (subst f (KVari x)))
    | KFixN(o,f) ->
       kfixn (binder_name f) (kn (neg pos) o) (fun x -> fn pos (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KMRec(_,k) -> assert (pos = Pos); fn pos k
    | KNRec(_,k) -> assert (pos = Neg); fn pos k
    | KDefi(d,os,ks) ->
       kdefi d
         (Array.mapi (fun i o -> kn (compose d.tdef_ovariance.(i) pos) o) os)
         (Array.mapi (fun i k -> fn (compose d.tdef_kvariance.(i) pos) k) ks)
    | KUVar(u,os) -> kuvar u (Array.map lift_ordinal os)
    | KUCst(t,f,cl) -> kucst (binder_name f) (box t) (fun x -> fn pos (subst f (KVari x)))
    | KECst(t,f,cl) -> kecst (binder_name f) (box t) (fun x -> fn pos (subst f (KVari x)))
  in
  if pos = Pos || pos = Neg then (
    unbox (mvbind mk_free_ovari (mbinder_names k)
             (fun xs -> fn pos (msubst k (Array.map (fun x -> OVari x) xs)))))
  else k

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
      | KUVar(u,_) -> assert(!(u.uvar_val) = None); if eq_uvar v u then x else box k
                      (* TODO: is it ok to ignore ordinal parameters ? *)
      | KVari(x)   -> box_of_var x
      | KDefi(d,o,a) -> kdefi d (Array.map gn o) (Array.map fn a)
      | KMRec(_,k)
      | KNRec(_,k) -> assert false (* NOTE: works because we do not infer type with
                                      KMRec as they are removed when setting
                                      a unification variable *)
      | KUCst(t,f,cl) -> kucst (binder_name f) (box t) (fun x -> fn (subst f (KVari x)))
      | KECst(t,f,cl) -> kecst (binder_name f) (box t) (fun x -> fn (subst f (KVari x)))
    and gn o =
      match orepr o with
      | OVari x -> box_of_var x
      | OSucc o -> osucc (gn o)
      | o -> box o
    in
    fn k))

(****************************************************************************
 *                Set kuvar with kind.                                      *
 *                     - use the previous function 'make_safe'              *
 *                     - does the occur check                               *
 *                     - if the kuvar_state is not Free, is uses the state  *
 *                       and ignore the arguemt. Therefore it is not safe   *
 *                       to assume that the unification variable is         *
 *                       related to k after seting                          *
 ****************************************************************************)

let safe_set_kuvar : occur -> kuvar -> kind from_ords -> ordinal array -> unit =
  fun side v k os ->
    assert(!(v.uvar_val) = None);
  (* side = Pos means we are checking k < KUVar(u,os)
     side = Neg means we are chacking KUVar(u,os) < k
     side <> Pos and Neg means we not in the previous cases *)
  let k =
    match !(v.uvar_state) with
    | Free -> k
    | Sum l -> mbind_assoc kdsum v.uvar_arity l
    (* TODO: on jette k ... normal mais bof, devrait être mieux traité *)
    | Prod l -> mbind_assoc kprod v.uvar_arity l
  in
  assert (mbinder_arity k = v.uvar_arity);
  let k = make_safe side v k in
  let k =
    match kuvar_occur ~safe_ordinals:os v (msubst k (Array.make v.uvar_arity OConv)) with
    | Non -> k
    | Pos -> constant_mbind v.uvar_arity (
      KFixM(OConv,bind_kuvar v (msubst k (Array.make v.uvar_arity OConv))))
    | _   ->
       match side with
       | Neg -> constant_mbind v.uvar_arity bot
       | Pos -> constant_mbind v.uvar_arity top
       | _ -> raise Occur_check
  in
  set_kuvar v k

(****************************************************************************
 *                 bindings of ordinals in type and ordinals                *
 ****************************************************************************)

(* The main difficulty here is for unification variable for kind or ordinals
    If we bind o in a variable ?1(o1,...,on) that may use o while o is not
    among its parameter, we must create a new variable ?2 and set
    ?1(x1,...,xn) to ?2(x1,...,xn,o). This appends in general for more
   than one variable. See the comment in the KUVar and OUVar cases *)

let index len os x u =
  let rec fn i =
    if i >= len then raise Not_found else (
      if strict_eq_ordinal os.(i) u then x.(i) else
        fn (i+1))
  in
  fn 0


let rec bind_fn ?(from_generalise=false) len os x k = (
  let fn = bind_fn ~from_generalise len os x in
  let gn = bind_gn ~from_generalise len os x in
  let k = repr k in
  let res = match repr k with
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
    | KMRec(_,k)
    | KNRec(_,k)   -> fn k (* NOTE: safe, because erased in generalise with safe assertion, and
                              subtyping is called later when used to instanciate unif var,
                              so if unsafe, subtyping/eq_kind/leq_kind will fail *)
    | KUVar(u,os') ->
       let os'' = List.filter (fun o ->
         not (Array.exists (strict_eq_ordinal o) os') && not (kuvar_ord_occur u o))
         (Array.to_list os)
       in
       (* nothing to do *)
       if os'' = [] then
         kuvar u (Array.map gn os')
       else
         (* if the variable value is recursive, we fix its value
            or produce occur_check now, otherwise it loops *)
         let is_recursive =
           match !(u.uvar_state) with
           | Free -> Non
           | Sum l | Prod l -> List.fold_left (fun acc (_,k) ->
             combine acc (kuvar_occur u (msubst k os'))) Non l
         in
         if is_recursive <> Non then
           (safe_set_kuvar Non u (constant_mbind 0 (KProd [] (*ignored anyway*))) os';
            fn k)
       else
         (* general case *)
         let os'' = Array.of_list os'' in
         let new_ords = Array.append os' os'' in
         let new_len = u.uvar_arity + Array.length os'' in
         let state =
           match !(u.uvar_state) with
           | Free -> Free
           | Sum l ->
              Sum (List.map (fun (s,f) ->
                (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_fn ~from_generalise new_len new_ords x (msubst f os'))))) l)
           | Prod l ->
              Prod (List.map (fun (s,f) ->
                (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_fn ~from_generalise new_len new_ords x (msubst f os'))))) l)
         in
         let v = new_kuvara ~state (u.uvar_arity + Array.length os'') in
         let k = unbox (mbind mk_free_ovari (Array.make u.uvar_arity "α") (fun x ->
           kuvar v (Array.init new_len
                      (fun i -> if i < u.uvar_arity then x.(i) else box
                          (match os''.(i - u.uvar_arity) with
                          | OVari _ -> OConv
                          (* TODO: not clean: OVari represents OConv in generalise *)
                          | o -> o)))))
         in
         Io.log_uni "set in bind fn\n%!";
         set_kuvar u k;
         kuvar v (Array.map gn new_ords)
    | KUCst(t,f,cl) | KECst(t,f,cl) when from_generalise || len = 0 ->
       if cl then box k else lift_kind k
    | KUCst(t,f,_) ->
         kucst (binder_name f) (box t) (fun x -> fn (subst f (KVari x)))
    | KECst(t,f,_) ->
         kecst (binder_name f) (box t) (fun x -> fn (subst f (KVari x)))

  in
  if Bindlib.is_closed res then box k else res)


and bind_gn ?(from_generalise=false) len os x o = (
  let fn = bind_fn ~from_generalise len os x in
  let gn = bind_gn ~from_generalise len os x in
  let o = orepr o in
  try
    index len os x o
  with
    Not_found ->
      let res =
        match orepr o with
        | OConv    -> box OConv
        | OVari(x) -> box_of_var x
        | OSucc(o) -> osucc (gn o)
        | OLess(o,In(t,f)) ->
           oless_In (gn o) (map_term fn t)
             (vbind mk_free_ovari (binder_name f)
                (fun x -> fn (subst f (OVari x))))
        | OLess(o,NotIn(t,f)) ->
           oless_NotIn (gn o) (map_term fn t)
             (vbind mk_free_ovari (binder_name f)
                (fun x -> fn (subst f (OVari x))))
        | OLess(o,Gen(i,rel,f)) ->
           oless_Gen (gn o) i rel
             (mvbind mk_free_ovari (mbinder_names f)
                (fun x -> let k1,k2 = msubst f (Array.map free_of x) in
                          box_pair (fn k1) (fn k2)))
        | OUVar(u,os') ->
           let os'' = List.filter (fun o ->
             not (Array.exists (strict_eq_ordinal o) os') &&
               (not (ouvar_occur u o)))
             (Array.to_list os)
           in
           if os'' = [] then
             ouvar u (Array.map gn os')
           else
             let os'' = Array.of_list os'' in
             let new_os = Array.append os' os'' in
             let new_len = Array.length new_os in
             let upper = match snd u.uvar_state with
               | None -> None
               | Some o ->
                  let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                    bind_gn ~from_generalise new_len new_os x (msubst o os'))
                  in
                  assert (is_closed f);
                  Some (unbox f)
             in
             let lower = match fst u.uvar_state with
               | None -> None
               | Some o ->
                  let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                    bind_gn ~from_generalise new_len new_os x (msubst o os'))
                  in
                  assert (is_closed f);
                  Some (unbox f)
             in
             let v = new_ouvara ?lower ?upper new_len in
             let k = unbox (mbind mk_free_ovari (Array.make u.uvar_arity "α") (fun x ->
               ouvar v (Array.init new_len (fun i ->
                 if i < u.uvar_arity then x.(i) else
                   box (match os''.(i - u.uvar_arity) with
                   | OVari _ -> OConv
                          (* TODO: not clean: OVari represents OConv in generalise *)
                   | o -> o)))))
             in
             Io.log_uni "set in bind gn\n%!";
             set_ouvar u k;
             ouvar v (Array.map gn new_os)
      in
      if Bindlib.is_closed res then box o else res)

let obind_ordinals : ordinal array -> ordinal -> (ordinal, ordinal) mbinder = fun os o ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x ->
    bind_gn len os x o))

let bind_ordinals : ordinal array -> kind -> (ordinal, kind) mbinder = fun os k ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x -> bind_fn len os x k))

let bind_ouvar : ouvar -> kind -> (ordinal, kind) binder = fun v k ->
  unbox (bind mk_free_ovari "α" (fun x ->
    bind_fn 1 [|OUVar(v,[||])|] [|x|] k))

let _ = fbind_ordinals := bind_ordinals
let _ = fobind_ordinals := obind_ordinals

(****************************************************************************
 *                    Decomposition type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

(* This function index all the ordinal in two kinds,
   select the usefull par of the context and return
   the usefull relations between two ordinals *)
let generalise : ordinal list -> kind -> kind ->
  int list * (int * int) list * (ordinal, kind * kind) mbinder * (int * ordinal) list
  = fun pos k1 k2 ->

  (* will of the table of all ordinals in the type to generalize them.
     the ordinal will be ovari when it replaces an infinite ordinals (see TODO
     in bind_fn and bind_gn.

     The integer, is a temporary index,
     The variable is the future variable to be bound using bind_fn
     The boolean ref is to know if the variable occurs in the formula *)

  let res : (ordinal * (int * ovar * bool ref)) list ref = ref [] in
  (* ocunter for the index above *)
  let i = ref 0 in
  (* This table will keep the relation (o, o') when o = OLess(o',_) *)
  let relation : (int * int) list ref = ref [] in

  let rec eps_search keep o =
    match o with
    | OLess(o',w) ->
       (try
          let (n,v,k) = assoc_ordinal o !res in
          k := !k || keep;
          (n,o)
        with
          Not_found ->
            let n = !i in incr i;
            let v = new_ovari ("o_" ^ string_of_int n) in
            res := (o, (n, v, ref keep)) :: !res;
            if o' <> OConv then (
                let (p, _) = eps_search false o' in
                relation := (n,p)::!relation);
            (n, o))
    | o -> assert false
  and search pos o =
    let o = orepr o in
    let res =
      match o with
      | OLess _ -> let (_, o) = eps_search true o in box o
      | OSucc o -> osucc(search pos o)
      | OVari o -> box_of_var o
      | OUVar({uvar_state = (Some o', _)} as u, os) when pos = Neg ->
         set_ouvar u o'; search pos o (* NOTE: avoid looping in flot.typ/compose *)
      | OUVar(u,os) ->
         (match fst u.uvar_state with
         | None -> ()
         | Some f -> ignore (search All (msubst f os)));
         (match snd u.uvar_state with
         | None -> ()
         | Some f -> ignore (search All (msubst f os)));
         ouvar u (Array.map (search All) os)
      | OConv when pos = Pos ->
         let n = !i in incr i;
         let v = new_ovari ("o_" ^ string_of_int n) in
         res := (free_of v, (n, v, ref true)) :: !res; box_of_var v
      | OConv   -> box OConv
    in
    res
  and fn pos k =
    match full_repr k with
    | KFunc(a,b) -> kfunc (fn (neg pos) a) (fn pos b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn pos a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn pos a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn pos (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn pos (subst f (OVari x)))
    | KFixM(o,f) -> kfixm (binder_name f) (search (neg pos) o)
       (fun x -> fn pos (subst f (KVari x)))
    | KFixN(o,f) -> kfixn (binder_name f) (search pos o)
       (fun x -> fn pos (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KMRec(_,k)
    | KNRec(_,k) -> assert false (* dealt with before in subtype *)
    | KUVar(u,os) -> kuvar u (Array.map (search All) os)
    | KDefi(td,os,ks)    -> assert false (* TODO: should not open definition, and use
                                            variance for ordinal parameters, if the definition
                                            has no mu/nu *)
    | KUCst(t,f,cl) | KECst(t,f,cl) -> (* No generalisation of ordinals in witness *)
       if cl then box k else lift_kind k


  in
  let k1 = unbox (fn Neg k1) in
  let k2 = unbox (fn Pos k2) in

  let pos = List.map (fun o -> fst (eps_search false o)) pos in
  let res = List.filter (fun (o,(n,v,k)) -> !k) !res in
  let ovars = Array.of_list (List.map (fun (o,(n,v,_)) -> v) res) in
  let ords  = Array.of_list (List.map (fun (o,(n,v,_)) -> o) res) in
  Io.log_uni "bind in generalise\n%!";
  let k1 = bind_fn ~from_generalise:true (Array.length ovars) ords (Array.map box_of_var ovars) k1 in
  let k2 = bind_fn ~from_generalise:true (Array.length ovars) ords (Array.map box_of_var ovars) k2 in
  let both = box_pair k1 k2 in
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

  Io.log_sub "generalise pos: %a\n%!" (fun ff l -> List.iter (Format.fprintf ff "%d ") l) pos;
  Io.log_sub "generalise rel: %a\n%!" (fun ff l -> List.iter (fun (a,b) ->
    Format.fprintf ff "(%d,%d) "a b) l) rel;
  Io.log_sub "generalise os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
    Format.fprintf ff "(%d,%a) "n (!fprint_ordinal false) o) l) os;

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
              let v = search (List.assoc i rel) in
              new_ouvar ~upper:(constant_mbind 0 v) ()
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
    Io.log_sub "recompose os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
        Format.fprintf ff "(%d,%a) "n (!fprint_ordinal false) o) l) os;
    os, pos, k1, k2

(* Matching kind, used for printing only *)

let rec match_kind : kuvar list -> ouvar list -> kind -> kind -> bool = fun kuvars ouvars p k ->
  let res = match full_repr p, full_repr k with
  | KUVar(ua,[||]), k when List.memq ua kuvars ->
     set_kuvar ua (constant_mbind 0 k); true
  | KFunc(p1,p2), KFunc(k1,k2) ->
     match_kind kuvars ouvars p1 k1 && match_kind kuvars ouvars p2 k2
  | KDSum(ps1), KDSum(ps2)
  | KProd(ps1), KProd(ps2) ->
     List.length ps1 = List.length ps2 &&
     let ps1 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps1 in
     let ps2 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps2 in
     List.for_all2 (fun (s1,p1) (s2,k1) ->
       s1 = s2 && match_kind kuvars ouvars p1 k1) ps1 ps2
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
    | OUVar(uo,_), o when List.memq uo ouvars ->
       set_ouvar uo (constant_mbind 0 o); true
    | OSucc(p), OSucc(o) -> match_ordinal ouvars p o
    | p, k -> strict_eq_ordinal p k in
  res
