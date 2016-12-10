(****************************************************************************)
(**{3                    binding relating functions                        }*)
(****************************************************************************)

open Ast
open Position
open Bindlib
open Term
open Compare

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
      | OConv   -> oconv
      | _ -> assert false
    in
    fn k))

(****************************************************************************
 *                    Increase ordinals in covariant position               *
 *                      that cannot be used by the variable u               *
 *                       to allow setting the value of an uvar              *
 ****************************************************************************)

(* FIXME: pos is the polarity of the variable u, not k , this is not natural, should be inversed *)
let make_safe pos u k =
  let rec gn o = match orepr o with
    | OLess(o',_) as o when kuvar_ord_occur u o -> gn o'
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
 *                Set kuvar with kind.                                      *
 *                     - use the previous function 'make_safe'              *
 *                     - does the occur check                               *
 *                     - if the kuvar_state is not Free, is uses the state  *
 *                       and ignore the arguemt. Therefore it is not safe   *
 *                       to assume that the unification variable is         *
 *                       related to k after seting                          *
 ****************************************************************************)
exception Occur_check

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
