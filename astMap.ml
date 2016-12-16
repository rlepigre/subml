(****************************************************************************)
(**{3                      Mapping of kind and ordinals                    }*)
(****************************************************************************)

open Ast
open Bindlib

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
