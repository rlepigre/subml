(****************************************************************************)
(**{3                    Binding relating functions                        }*)
(****************************************************************************)

open Ast
open Position
open Bindlib
open Term
open Compare
open AstMap

(****************************************************************************)
(**{2               bindings of a type in a type and ordinals              }*)
(****************************************************************************)

(** binding a unification variable in a kind *)
let bind_kuvar : kuvar -> kind -> (kind, kind) binder = fun v k ->
  unbox (bind mk_free_kvari "X" (fun x ->
    let fkind _ k self_kind _ def_kind =
      match repr k with
      | KUVar(u,_) -> assert(is_unset u); if eq_uvar v u then x else box k
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
      argumemt. Therefore it is not safe to assume that the unification
      variables is related to k after seting
*)
let safe_set_kuvar : occur -> kuvar -> kind from_ordis -> ordi array -> unit =
  fun side v k os ->
      (* side = Pos means we are checking k < KUVar(u,os)
         side = Neg means we are chacking KUVar(u,os) < k
         side <> Pos and Neg means we not in the previous cases *)
    let k =
      match uvar_state v with
      | Free -> k
      | DSum l -> mbind_assoc kdsum v.uvar_arity l
        (* TODO: on jette k ... normal mais bof, devrait être mieux traité *)
      | Prod l -> mbind_assoc kprod v.uvar_arity l
    in
    assert (mbinder_arity k = v.uvar_arity);
    let k =
      match kuvar_occur ~safe_ordis:os v (msubst k (Array.make v.uvar_arity OConv)) with
      | Non   -> k
      | Pos _ -> constant_mbind v.uvar_arity (
        KFixM(OConv,bind_kuvar v (msubst k (Array.make v.uvar_arity OConv))))
      | _     ->
         match side with
         | Neg _ -> constant_mbind v.uvar_arity bot
         | Pos _ -> constant_mbind v.uvar_arity top
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
      if strict_eq_ordi os.(i) u then x.(i) else
        fn (i+1))
  in
  fn 0

let rec bind_both ?(from_generalise=false) os x =
  let fresh_uvar = ref [] in
  let fresh_ovar = ref [] in
  let fkind _ k (self_kind:self_kind) (self_ord:self_ord) def_kind =
    let res = match repr k with
    | KMRec(_,k)
    | KNRec(_,k)   -> self_kind k
    (* NOTE: safe, because forbidden in generalise, and
       subtyping is called later when used to instanciate unif var,
       so if unsafe, subtyping/eq_kind/leq_kind will fail *)
    | KUVar(u,_)   when List.mem_assq u !fresh_uvar -> kuvar u (List.assq u !fresh_uvar)
    | KUVar(u,os') ->
       let os'' = List.filter (fun o ->
         not (Array.exists (strict_eq_ordi o) os') && not (kuvar_ord_occur u o))
         (Array.to_list os)
       in
       (* nothing to do *)
       if os'' = [] then
         kuvar u (Array.map self_ord os')
       else
         (* if the variable value is recursive, we fix its value
            or produce occur_check now, otherwise it loops *)
         let is_recursive =
           match uvar_state u with
           | Free -> Non
           | DSum l | Prod l -> List.fold_left (fun acc (_,k) ->
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
           match uvar_state u with
           | Free -> Free
           | DSum l ->
              DSum (List.map (fun (s,f) ->
                (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_fn ~from_generalise new_ords x (msubst f os'))))) l)
           | Prod l ->
              Prod (List.map (fun (s,f) ->
                (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_fn ~from_generalise new_ords x (msubst f os'))))) l)
         in
         let v = new_kuvara ~state (u.uvar_arity + Array.length os'') in
         let new_ords = Array.map self_ord new_ords in
         fresh_uvar := (v, new_ords) :: !fresh_uvar;
         let k = unbox (mbind mk_free_ovari (Array.make u.uvar_arity "α") (fun x ->
           kuvar v (Array.init new_len
                      (fun i -> if i < u.uvar_arity then x.(i) else box
                          (match os''.(i - u.uvar_arity) with
                          | OVari _ -> OConv
                          (* TODO: not clean: OVari represents OConv in generalise *)
                          | o -> o)))))
         in
         set_kuvar u k;
         kuvar v new_ords
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
      | OUVar(u,_)   when List.mem_assq u !fresh_ovar -> ouvar u (List.assq u !fresh_ovar)
      | OUVar(u,os') ->
         let os'' = List.filter (fun o ->
           not (Array.exists (strict_eq_ordi o) os') &&
             (not (ouvar_occur u o)))
           (Array.to_list os)
         in
         if os'' = [] then
           ouvar u (Array.map self_ord os')
         else
           let os'' = Array.of_list os'' in
           let new_os = Array.append os' os'' in
           let new_len = Array.length new_os in
           assert (is_unset u);
           let upper = match snd (uvar_state u) with
             | None -> None
             | Some o ->
                let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_gn ~from_generalise new_os x (msubst o os'))
                in
                assert (is_closed f);
                Some (unbox f)
           in
           assert (is_unset u);
           let lower = match fst (uvar_state u) with
             | None -> None
             | Some o ->
                let f = mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                  bind_gn ~from_generalise new_os x (msubst o os'))
                in
                assert (is_closed f);
                Some (unbox f)
           in
           let v = new_ouvara ?lower ?upper new_len in
           let new_os = Array.map self_ord new_os in
           fresh_ovar := (v, new_os) :: !fresh_ovar;
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
           ouvar v new_os
      | o -> def_ord o
      in
      if Bindlib.is_closed res then box o else res
  in
  (map_kind ~fkind ~ford, map_ordi ~fkind ~ford)

(** [bind_fn ?(from_generalise=false) os x k]
    Bind an array [os] of ordinals in the kind [k]. [x] is the array
    of bindlib variables to be used *)
and bind_fn ?(from_generalise=false) os x k =
  (fst (bind_both ~from_generalise os x):?occ:occur -> kind -> kbox) ~occ:sPos k

(** [bind_gn ?(from_generalise=false) len os x o]
    Bind an array [os] of ordinals in the ordinal [o]. [x] is the array
    of bindlib variables to be used *)
and bind_gn ?(from_generalise=false) os x o =
  (snd (bind_both ~from_generalise os x):?occ:occur -> ordi -> obox) ~occ:sPos o

(** binding ordinals in one ordinal *)
let obind_ordis : ordi array -> ordi -> (ordi, ordi) mbinder = fun os o ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x ->
    bind_gn os x o))

(** binding ordinals in one kind *)
let bind_ordis : ordi array -> kind -> (ordi, kind) mbinder = fun os k ->
  let len = Array.length os in
  unbox (mbind mk_free_ovari (Array.make len "α") (fun x -> bind_fn os x k))

(** binding of one ordinal in one kind *)
let bind_ouvar : ouvar -> kind -> (ordi, kind) binder = fun v k ->
  unbox (bind mk_free_ovari "α" (fun x ->
    bind_fn [|OUVar(v,[||])|] [|x|] k))

(** [bind_ordinals] and [obind_ordinals] are needed in compare,
     hence we set the pointers defined in compare *)
let _ = fbind_ordis := bind_ordis
let _ = fobind_ordis := obind_ordis
