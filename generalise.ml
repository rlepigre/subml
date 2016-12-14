(****************************************************************************)
(**{3                 Functions related to generalisation                  }*)
(****************************************************************************)

open Ast
open Compare
open Position
open Bindlib
open Format
open Term
open Binding
open Print

(****************************************************************************
 *                    Decomposition type, ordinals                          *
 *             includes compression of consecutive mus and nus              *
 ****************************************************************************)

exception FailGeneralise

(** This function index all the ordinal in two kinds,
    select the usefull part of the context and returns
    the usefull relations between two ordinals. It also
    returns the index of the ordinals *)
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
  and search occ o =
    let o = orepr o in
    let res =
      match o with
      | OLess _ -> let (_, o) = eps_search true o in box o
      | OSucc o -> osucc(search occ o)
      | OVari o -> box_of_var o
      | OUVar({uvar_state = (Some o', _)} as u, os) when occ = Neg ->
         set_ouvar u o'; search occ o (* NOTE: avoid looping in flot.typ/comocce *)
      | OUVar(u,os) ->
         (match fst u.uvar_state with
         | None -> ()
         | Some f -> ignore (search All (msubst f os)));
         (match snd u.uvar_state with
         | None -> ()
         | Some f -> ignore (search All (msubst f os)));
         ouvar u (Array.map (search All) os)
      | OConv when occ = Pos ->
         let n = !i in incr i;
         let v = new_ovari ("o_" ^ string_of_int n) in
         res := (free_of v, (n, v, ref true)) :: !res; box_of_var v
      | OConv   -> box OConv
    in
    res
  and fn occ k =
    match full_repr k with
    | KFunc(a,b) -> kfunc (fn (neg occ) a) (fn occ b)
    | KProd(fs)  -> kprod (List.map (fun (l,a) -> (l, fn occ a)) fs)
    | KDSum(cs)  -> kdsum (List.map (fun (c,a) -> (c, fn occ a)) cs)
    | KKAll(f)   -> kkall (binder_name f) (fun x -> fn occ (subst f (KVari x)))
    | KKExi(f)   -> kkexi (binder_name f) (fun x -> fn occ (subst f (KVari x)))
    | KOAll(f)   -> koall (binder_name f) (fun x -> fn occ (subst f (OVari x)))
    | KOExi(f)   -> koexi (binder_name f) (fun x -> fn occ (subst f (OVari x)))
    | KFixM(o,f) -> kfixm (binder_name f) (search (neg occ) o)
       (fun x -> fn occ (subst f (KVari x)))
    | KFixN(o,f) -> kfixn (binder_name f) (search occ o)
       (fun x -> fn occ (subst f (KVari x)))
    | KVari(x)   -> box_of_var x
    | KMRec(_,k)
    | KNRec(_,k) -> raise FailGeneralise
    | KUVar(u,os) -> kuvar u (Array.map (search All) os)
    | KDefi(td,os,ks) -> assert false (* TODO: should not open definition, and use
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
  let k1 = bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k1 in
  let k2 = bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k2 in
  let both = box_pair k1 k2 in
  let both = unbox (bind_mvar ovars both) in
  let tbl = List.mapi (fun i (o,(n,v,k)) -> (n,i)) res in
  let os = List.map (fun (o,(n,v,_)) -> (List.assoc n tbl, o)) res in

  let rec next start n =
    if List.exists (fun (q,_) -> n = q) tbl then n else
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

  Io.log_sub "generalise pos: %a\n%!"
    (fun ff l -> List.iter (Format.fprintf ff "%d ") l) pos;
  Io.log_sub "generalise rel: %a\n%!"
    (fun ff l -> List.iter (fun (a,b) ->
    Format.fprintf ff "(%d,%d) "a b) l) rel;
  Io.log_sub "generalise os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
    Format.fprintf ff "(%d,%a) "n (print_ordinal false) o) l) os;

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
        Format.fprintf ff "(%d,%a) "n (print_ordinal false) o) l) os;
    os, pos, k1, k2

(* FIXME: what to do with duplicates, probably OK *)
let kuvar_list : kind -> (kuvar * ordinal array) list = fun k ->
  let r = ref [] in
  let adone = ref [] in
  let rec fn k =
    let k = repr k in
    if List.memq k !adone then () else (
    adone := k::!adone;
    match k with
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f OConv)
    | KUVar(u,os)  ->
       begin
         match !(u.uvar_state) with
         | Free -> ()
         | Sum l | Prod l ->
            List.iter (fun (c,f) -> fn (msubst f (Array.make (mbinder_arity f) OConv))) l
       end;
       if not (List.exists (fun (u',_) -> eq_uvar u u') !r) then
         r := (u,os) :: !r
    | KDefi(d,_,a) -> Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd [])))
  in
  fn k; !r

let ouvar_list : kind -> ouvar list = fun k ->
  let r = ref [] in
  let adone = ref [] in
  let rec fn k =
    let k = repr k in
    if List.memq k !adone then () else (
    adone := k::!adone;
    match k with
    | KUVar(_,_)   -> () (* ignore ordinals, will be constant *)
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> gn o; fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f OConv)
    | KDefi(d,o,a) -> Array.iter gn o;  Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd [])))
  and gn o =
    match orepr o with
    | OSucc(o)   -> gn o
    | OUVar(v,_) -> if not (List.exists (eq_uvar v) !r) then r := v :: !r
    | OConv      -> ()
    | OLess _    -> ()
    | OVari _    -> ()
  in
  fn k; !r

(* Matching kind, used for printing only *)
let rec match_kind : kuvar list -> ouvar list -> kind -> kind -> bool
  = fun kuvars ouvars p k ->
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
