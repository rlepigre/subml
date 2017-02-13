(****************************************************************************)
(**{3                      Mapping of kind and ordinals                    }*)
(****************************************************************************)

open Ast
open Bindlib

(** Mapping functions allows to apply some treatment to some constructors
    and use the default treatment to recurse for the other constructor.

    The output of Mapping function are bindlib's boxes, so you can
    use Mapping functions to bind some variables in a kind or ordinal *)

type self_kind = ?occ:occur -> kind -> kbox
type self_ord  = ?occ:occur -> ordi -> obox

(** [map_kind] and [map_ord] are the type of the function you need to write
    to define your own ast mapper. They receive in argument
    1°) the variance of the current kind/ordinal
    2°) the kind/ordinal itself
    3°) the function of type [self_kind] corresponding to a recursive call
        for kind
    4°) the function of type [self_ord] corresponding to a recursive call
        for ordinals
    5°) the function for to call to get the defaut behavious (which copy the
        Ast.
 *)
type map_kind  = occur -> kind -> self_kind -> self_ord -> (kind -> kbox) -> kbox
type map_ord   = occur -> ordi -> self_kind -> self_ord -> (ordi -> obox) -> obox


(** Mapping for kinds. The default value of the argument would just
    copy the kind ast. *)
let rec map_kind : ?fkind:map_kind -> ?ford:map_ord -> self_kind
  = fun ?(fkind=fun _ k _ _ defk -> defk ( repr k))
        ?(ford =fun _ o _ _ defo -> defo (orepr o))
        ?(occ=sPos) k ->
  let map_kind: ?occ:occur -> kind -> kbox = map_kind ~fkind ~ford in
  let map_ordi: ?occ:occur -> ordi -> obox  = map_ordi ~fkind ~ford in
  fkind occ k map_kind map_ordi (
    function
    | KFunc(a,b)   -> kfunc (map_kind ~occ:(neg occ) a) (map_kind ~occ b)
    | KProd(fs,e)  -> kprod e (List.map (fun (l,a) -> (l, map_kind ~occ a)) fs)
    | KDSum(cs)    -> kdsum (List.map (fun (c,a) -> (c, map_kind ~occ a)) cs)
    | KKAll(f)     -> kkall (binder_name f) (fun x -> map_kind ~occ (subst f (KVari x)))
    | KKExi(f)     -> kkexi (binder_name f) (fun x -> map_kind ~occ (subst f (KVari x)))
    | KOAll(f)     -> koall (binder_name f) (fun x -> map_kind ~occ (subst f (OVari x)))
    | KOExi(f)     -> koexi (binder_name f) (fun x -> map_kind ~occ (subst f (OVari x)))
    | KFixM(o,f)   -> kfixm (binder_name f) (map_ordi ~occ o)
                        (fun x -> map_kind  ~occ (subst f (KVari x)))
    | KFixN(o,f)   -> kfixn (binder_name f) (map_ordi ~occ:(neg occ) o)
                        (fun x -> map_kind  ~occ (subst f (KVari x)))
    | KVari(x)     -> box_of_var x
    | KDefi(d,o,a) -> let fn i =
                        map_ordi ~occ:(compose d.tdef_ovariance.(i) occ)
                      in
                      let gn i =
                        map_kind ~occ:(compose d.tdef_kvariance.(i) occ)
                      in
                      kdefi d (Array.mapi fn o) (Array.mapi gn a)
    | KMRec _
    | KNRec _      -> assert false
    | KUVar(u,os)  -> kuvar u (Array.map (map_ordi ~occ:All) os)
    | KUCst(_,_,c)
    | KECst(_,_,c) when c -> box k (* binder is closed *)
    | KUCst(t,f,_) -> kucst (binder_name f) (box t)
                        (fun x -> map_kind ~occ:All (subst f (KVari x)))
    | KECst(t,f,_) -> kecst (binder_name f) (box t)
                        (fun x -> map_kind ~occ:All (subst f (KVari x)))
    | KPrnt _      -> box k)


(** Mapping for ordinals. The default value of the argument would just
    copy the ordinal ast. *)
and map_ordi : ?fkind:map_kind -> ?ford:map_ord -> self_ord
  = fun ?(fkind=fun _ k _ _ defk -> defk (repr k))
        ?(ford=fun _ o _ _ defo -> defo (orepr o))
        ?(occ=sPos) o ->
  let map_kind = map_kind ~fkind ~ford in
  let map_ordi = map_ordi ~fkind ~ford in
  ford occ o map_kind map_ordi (
    function
    | OVari x -> box_of_var x
    | OVars s -> box (OVars s)
    | OSucc o -> osucc (map_ordi ~occ o)
    | OLess(o,In(t,w))  -> oless_In (map_ordi ~occ o) (box t)
       (vbind mk_free_o (binder_name w) (fun x -> map_kind ~occ:All (subst w (OVari x))))
    | OLess(o,NotIn(t,w))  -> oless_NotIn (map_ordi ~occ o) (box t)
       (vbind mk_free_o (binder_name w) (fun x -> map_kind ~occ:All (subst w (OVari x))))
    | OLess(o,Gen(i,s))  ->
       let f p = { s with sch_judge = p } in
       let p = s.sch_judge in
       let s = box_apply f
         (mvbind mk_free_o (mbinder_names p) (fun xs ->
           let k1, k2 = msubst p (Array.map (fun x -> OVari x) xs) in
           box_pair (match k1 with
           | SchTerm t -> box (SchTerm t)
           | SchKind k -> box_apply (fun k -> SchKind k) (map_kind ~occ:All k))
             (map_kind ~occ:All k2)))
       in
       oless_Gen (map_ordi ~occ o) i s

    | OUVar(u,os) -> ouvar u (Array.map (map_ordi ~occ:All) os)
    | OConv -> box o)
