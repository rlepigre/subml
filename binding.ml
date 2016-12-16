(****************************************************************************)
(**{3                    binding relating functions                        }*)
(****************************************************************************)

open Ast
open Position
open Bindlib
open Term
open Compare

(****************************************************************************)
(**{2                      lifting of kind and ordinals                    }*)
(****************************************************************************)

(** Mapping function are used to push back data structure in bindlib boxes.
    This allows to bind the variables in this structure. *)

type self_kind = ?occ:occur -> kind -> kbox
type self_ord  = ?occ:occur -> ordinal -> obox
type map_kind  = occur -> kind -> self_kind -> self_ord -> (kind -> kbox) -> kbox
type map_ord   = occur -> ordinal -> self_kind -> self_ord -> (ordinal -> obox) -> obox

(** Mapping for kinds *)
let rec map_kind : ?fkind:map_kind -> ?ford:map_ord -> self_kind
  = fun ?(fkind=fun _ k _ _ defk -> defk ( repr k))
        ?(ford =fun _ o _ _ defo -> defo (orepr o))
        ?(occ=Pos) k ->
  let map_kind: ?occ:occur -> kind -> kbox = map_kind ~fkind ~ford in
  let map_ordinal: ?occ:occur -> ordinal -> obox  = map_ordinal ~fkind ~ford in
  fkind occ k map_kind map_ordinal (
    function
    | KFunc(a,b) -> kfunc (map_kind ~occ:(neg occ) a) (map_kind ~occ b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, map_kind ~occ a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, map_kind ~occ a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> map_kind ~occ (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> map_kind ~occ (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> map_kind ~occ (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> map_kind ~occ (subst f (OVari x)))
    | KFixM(o,f) ->
       kfixm (binder_name f) (map_ordinal ~occ o)
         (fun x -> map_kind  ~occ (subst f (KVari x)))
    | KFixN(o,f) ->
       kfixn (binder_name f) (map_ordinal ~occ:(neg occ) o)
         (fun x -> map_kind  ~occ (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KDefi(d,o,a) -> kdefi d (Array.mapi (fun i -> map_ordinal ~occ:(compose d.tdef_ovariance.(i) occ)) o)
                              (Array.mapi (fun i -> map_kind ~occ:(compose d.tdef_kvariance.(i) occ)) a)
    | KMRec _
    | KNRec _    -> assert false
    | KUVar(u,os)-> kuvar u (Array.map (map_ordinal ~occ:All) os)
    | KUCst(t,f,cl) ->
       if cl then box k else
         kucst (binder_name f) (box t) (fun x -> map_kind ~occ:All (subst f (KVari x)))
    | KECst(t,f,cl) ->
       if cl then box k else
         kecst (binder_name f) (box t) (fun x -> map_kind ~occ:All (subst f (KVari x))))


(** Mapping for ordinals *)
and map_ordinal : ?fkind:map_kind -> ?ford:map_ord -> self_ord
  = fun ?(fkind=fun _ k _ _ defk -> defk (repr k))
        ?(ford=fun _ o _ _ defo -> defo (orepr o))
        ?(occ=Pos) o ->
  let map_kind = map_kind ~fkind ~ford in
  let map_ordinal = map_ordinal ~fkind ~ford in
  ford occ o map_kind map_ordinal (
    function
    | OVari x -> box_of_var x
    | OSucc o -> osucc (map_ordinal ~occ o)
    | OLess(o,In(t,w))  -> oless_In (map_ordinal ~occ o) (box t)
       (vbind mk_free_ovari (binder_name w) (fun x -> map_kind ~occ:All (subst w (OVari x))))
    | OLess(o,NotIn(t,w))  -> oless_NotIn (map_ordinal ~occ o) (box t)
       (vbind mk_free_ovari (binder_name w) (fun x -> map_kind ~occ:All (subst w (OVari x))))
    | OLess(o,Gen(i,r,p))  ->
       oless_Gen (map_ordinal ~occ o) i r
         (mvbind mk_free_ovari (mbinder_names p) (fun xs ->
           let k1, k2 = msubst p (Array.map (fun x -> OVari x) xs) in
           box_pair (map_kind ~occ:All k1) (map_kind ~occ:All k2)))
    | OUVar(u,os) -> ouvar u (Array.map (map_ordinal ~occ:All) os)
    | OConv -> box o)


(****************************************************************************)
(**{2               bindings of a type in a type and ordinals              }*)
(****************************************************************************)

(** Increase ordinals in covariant position that cannot be used by the
    variable u to allow setting the value of an uvar
*)
let make_safe pos u k =
  let rec gn o = match orepr o with
    | OLess(o',_) as o when kuvar_ord_occur u o -> gn o'
    | o -> map_ordinal o
  in
  let kn pos o =
    if pos = Neg then gn o else map_ordinal o
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
    | KMRec(_,k) -> assert (pos = Neg); fn pos k
    | KNRec(_,k) -> assert (pos = Pos); fn pos k
    | KDefi(d,os,ks) ->
       kdefi d
         (Array.mapi (fun i o -> kn (compose d.tdef_ovariance.(i) pos) o) os)
         (Array.mapi (fun i k -> fn (compose d.tdef_kvariance.(i) pos) k) ks)
    | KUVar(u,os) -> kuvar u (Array.map map_ordinal os)
    | KUCst(t,f,cl) -> kucst (binder_name f) (box t) (fun x -> fn pos (subst f (KVari x)))
    | KECst(t,f,cl) -> kecst (binder_name f) (box t) (fun x -> fn pos (subst f (KVari x)))
  in
  if pos = Pos || pos = Neg then (
    unbox (mvbind mk_free_ovari (mbinder_names k)
             (fun xs -> fn pos (msubst k (Array.map (fun x -> OVari x) xs)))))
  else k

(** binding a unification variable in a kind *)
let bind_kuvar : kuvar -> kind -> (kind, kind) binder = fun v k ->
  unbox (bind mk_free_kvari "X" (fun x ->
    let fkind _ k self_kind _ def_kind =
      match repr k with
      | KUVar(u,_) -> assert(!(u.uvar_val) = None); if eq_uvar v u then x else box k
      | k -> def_kind k
    in
    map_kind ~fkind k))


(****************************************************************************)
(**{2                       Kind variable instanciation                    }*)
(****************************************************************************)

(** Raised by set_kuvar if instanciation is illegal because it
    creates cyclic types *)
exception Occur_check

(** Set kuvar with kind.
    - use the previous function 'make_safe'
    - does the occur check
    - if the kuvar_state is not Free, is uses the state and ignore the
      arguemt. Therefore it is not safe to assume that the unification
      variable is related to k after seting
*)
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
  let k = make_safe (neg side) v k in
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

(****************************************************************************)
(**{2               bindings of ordinals in type and ordinals              }*)
(****************************************************************************)

(** The main difficulty here is for unification variable for kind or ordinals
    If we bind o in a variable ?1(o1,...,on) that may use o while o is not
    among its parameter, we must create a new variable ?2 and set
    ?1(x1,...,xn) to ?2(x1,...,xn,o). This appends in general for more
   than one variable. See the comment in the KUVar and OUVar cases *)

(** [index os x u] searches the index [i] of [u] in [os] and returns [x.(i)] *)
let index os x u =
  let len = Array.length os in
  let rec fn i =
    if i >= len then raise Not_found else (
      if strict_eq_ordinal os.(i) u then x.(i) else
        fn (i+1))
  in
  fn 0

let rec bind_both ?(from_generalise=false) os x =
  let fkind _ k (self_kind:self_kind) (self_ord:self_ord) def_kind =
    let res = match repr k with
    | KMRec(_,k)
    | KNRec(_,k)   -> self_kind k
    (* NOTE: safe, because erased in generalise with safe assertion, and
       subtyping is called later when used to instanciate unif var,
       so if unsafe, subtyping/eq_kind/leq_kind will fail *)
    | KUVar(u,os') ->
       let os'' = List.filter (fun o ->
         not (Array.exists (strict_eq_ordinal o) os') && not (kuvar_ord_occur u o))
         (Array.to_list os)
       in
       (* nothing to do *)
       if os'' = [] then
         kuvar u (Array.map self_ord os')
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
            self_kind k)
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
                  bind_fn ~from_generalise new_ords x (msubst f os'))))) l)
           | Prod l ->
              Prod (List.map (fun (s,f) ->
                (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_fn ~from_generalise new_ords x (msubst f os'))))) l)
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
         set_kuvar u k;
         kuvar v (Array.map self_ord new_ords)
    | KUCst(t,f,cl) | KECst(t,f,cl) when from_generalise || os = [||] ->
         if cl then box k else map_kind k
    | k -> def_kind k
    in
    if Bindlib.is_closed res then box k else res
  in
  let ford _ o (self_kind:self_kind) (self_ord:self_ord) def_ord =
    let o = orepr o in
    let res =
      try  index os x o with Not_found ->
      match o with
      | OUVar(u,os') ->
         let os'' = List.filter (fun o ->
           not (Array.exists (strict_eq_ordinal o) os') &&
             (not (ouvar_occur u o)))
           (Array.to_list os)
         in
         if os'' = [] then
           ouvar u (Array.map self_ord os')
         else
           let os'' = Array.of_list os'' in
           let new_os = Array.append os' os'' in
           let new_len = Array.length new_os in
           let upper = match snd u.uvar_state with
             | None -> None
             | Some o ->
                let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_gn ~from_generalise new_os x (msubst o os'))
                in
                assert (is_closed f);
                Some (unbox f)
           in
           let lower = match fst u.uvar_state with
             | None -> None
             | Some o ->
                let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_gn ~from_generalise new_os x (msubst o os'))
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
           ouvar v (Array.map self_ord new_os)
      | o -> def_ord o
      in
      if Bindlib.is_closed res then box o else res
  in
  (map_kind ~fkind ~ford, map_ordinal ~fkind ~ford)

(** [bind_fn ?(from_generalise=false) os x k]
    Bind an array [os] of ordinals in the kind [k]. [x] is the array
    of bindlib variables to be used *)
and bind_fn ?(from_generalise=false) os x k = (fst (bind_both ~from_generalise os x):?occ:occur -> kind -> kbox) ~occ:Pos k

(** [bind_gn ?(from_generalise=false) len os x o]
    Bind an array [os] of ordinals in the ordinal [o]. [x] is the array
    of bindlib variables to be used *)
and bind_gn ?(from_generalise=false) os x o = (snd (bind_both ~from_generalise os x):?occ:occur -> ordinal -> obox) ~occ:Pos o

(** binding ordinals in one ordinal *)
let obind_ordinals : ordinal array -> ordinal -> (ordinal, ordinal) mbinder = fun os o ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x ->
    bind_gn os x o))

(** binding ordinals in one kind *)
let bind_ordinals : ordinal array -> kind -> (ordinal, kind) mbinder = fun os k ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x -> bind_fn os x k))

(** binding of one ordinal in one kind *)
let bind_ouvar : ouvar -> kind -> (ordinal, kind) binder = fun v k ->
  unbox (bind mk_free_ovari "α" (fun x ->
    bind_fn [|OUVar(v,[||])|] [|x|] k))

(** [bind_ordinals] and [obind_ordinals] are needed in compare,
     hence we set the pointers defined in compare *)
let _ = fbind_ordinals := bind_ordinals
let _ = fobind_ordinals := obind_ordinals

let rec do_dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in
     if binder_name f = s then c else do_dot_proj t (subst f c) s
  | k ->
     failwith "Illegal dot projection"


let dot_proj : tbox -> string -> kbox = fun x s ->
  let rec fn t = match t.elt with
    | TVari x -> fn (in_pos t.pos (free_of x))
    | TDefi(d) -> do_dot_proj t d.ttype s
    | TCnst(_,a,_,_) -> do_dot_proj t a s
    | _ -> failwith "Illegal dot projection"
  in
  box_apply fn x
