open Ast
open Position
open Bindlib
open Format

(***************************************************************************
*                             mapping on terms                             *
****************************************************************************)

let map_term : (kind -> kbox) -> term -> tbox = fun kn t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> tcoer t.pos (fn t) (kn k)
    | TVari(x)    -> tvari t.pos x
    | TAbst(ko,f) -> let ko = map_opt kn ko in
                     tabst t.pos ko (in_pos t.pos (binder_name f))
                       (fun x -> fn (subst f (TVari x)))
    | TFixY(b,n,f)-> tfixy t.pos b n (in_pos t.pos (binder_name f))
                       (fun x -> fn (subst f (TVari x)))
    | TKAbs(f)    -> tkabs t.pos (dummy_pos (binder_name f))
                       (fun x -> fn (subst f (KVari x)))
    | TOAbs(f)    -> toabs t.pos (dummy_pos (binder_name f))
                       (fun x -> fn (subst f (OVari x)))
    | TAppl(a,b)  -> tappl t.pos (fn a) (fn b)
    | TReco(fs)   -> treco t.pos (List.map (fun (s,a) -> (s, fn a)) fs)
    | TProj(a,s)  -> tproj t.pos (fn a) s
    | TCons(s,a)  -> tcons t.pos s (fn a)
    |TCase(a,fs,d)-> tcase t.pos (fn a) (List.map (fun (s,a) -> (s, fn a)) fs)
       (map_opt fn d)
    | TCnst(f,a,b,cl)-> if cl then box t else tcnst f (kn a) (kn b)
    | TDefi _ | TPrnt _ -> box t
  in
  let res = fn t in
  if is_closed res then box t else res

(*****************************************************************
 *              test if a term is normal in CBV                  *
 *****************************************************************)
let is_normal : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> fn t
    | TVari(x)    -> true
    | TAbst(_)    -> true
    | TFixY(_)    -> false
    | TKAbs(f)    -> fn (subst f (KProd []))
    | TOAbs(f)    -> fn (subst f (OConv))
    | TAppl(a,b)  -> false
    | TReco(fs)   -> List.for_all (fun (_,t) -> fn t) fs
    | TProj(a,s)  -> false
    | TCons(s,a)  -> fn a
    | TCase(a,_,_)-> false
    | TDefi(d)    -> fn d.value
    | TCnst _     -> true
    | TPrnt _     -> false
  in fn t

(*****************************************************************
 *              test if a term is neutral in CBV                 *
 *****************************************************************)
let is_neutral : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> fn t
    | TVari(x)    -> true
    | TAbst(_)    -> false
    | TFixY(_)    -> false
    | TKAbs(f)    -> fn (subst f (KProd []))
    | TOAbs(f)    -> fn (subst f (OConv))
    | TAppl(a,b)  -> fn a
    | TReco(fs)   -> false
    | TProj(a,s)  -> fn a
    | TCons(s,a)  -> false
    | TCase(a,_,_)-> fn a
    | TDefi(d)    -> true (* because we know the type *)
    | TCnst _     -> true
    | TPrnt _     -> false
  in fn t
