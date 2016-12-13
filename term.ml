(***************************************************************************)
(**{3                   Usefull fonction on terms                         }*)
(***************************************************************************)

open Ast
open Position
open Bindlib
open Format
open LibTools

(** Map all kind in a term with the given function *)
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
    | TAppl(a,b)  -> tappl t.pos (fn a) (fn b)
    | TReco(fs)   -> treco t.pos (List.map (fun (s,a) -> (s, fn a)) fs)
    | TProj(a,s)  -> tproj t.pos (fn a) s
    | TCons(s,a)  -> tcons t.pos s (fn a)
    |TCase(a,fs,d)-> tcase t.pos (fn a) (List.map (fun (s,a) -> (s, fn a)) fs)
       (map_opt fn d)
    | TCnst(f,a,b,cl)-> if cl then box t else tcnst f (kn a) (kn b)
    | TMLet(b,x,bt)->
       tmlet t.pos
         (mbinder_names b)
         (mbinder_names (msubst b (Array.make (mbinder_arity b) OConv)))
         (fun os ks -> kn (mmsubst b  (Array.map free_of os) (Array.map free_of ks)))
         (map_opt fn x)
         (fun os ks -> fn (mmsubst bt (Array.map free_of os) (Array.map free_of ks)))
    | TDefi _ | TPrnt _ -> box t
  in
  let res = fn t in
  if is_closed res then box t else res

(** Test if a term is in normal form for CBV *)
let is_normal : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TAbst(_)    -> true
    | TCnst _     -> true

    | TFixY(_)    -> false
    | TAppl(a,b)  -> false
    | TCase(a,_,_)-> false
    | TProj(a,s)  -> false
    | TPrnt _     -> false

    | TCoer(t,k)  -> fn t
    | TCons(s,a)  -> fn a
    | TDefi(d)    -> fn d.value
    | TReco(fs)   -> List.for_all (fun (_,t) -> fn t) fs

    | TMLet(b,x,bt)->
       let (oa, ka) = mmbinder_arities bt OConv in
       fn (mmsubst bt (Array.make oa OConv) (Array.make ka (KProd [])))

    | TVari(x)    -> assert false
  in fn t

(** Test if a term is neutral in CBV;
    This is not the exact definition of neutral.
    Here, we mean a term whose type in known
    with elimination or type decocation applied to it *)
let is_neutral : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(t,k)  -> true
    | TDefi(d)    -> true
    | TCnst _     -> true
    | TPrnt _     -> true

    | TCons(s,a)  -> false
    | TAbst(_)    -> false
    | TFixY(_)    -> false
    | TReco(fs)   -> false

    | TAppl(a,b)  -> fn a
    | TProj(a,s)  -> fn a
    | TCase(a,_,_)-> fn a

    | TMLet(b,x,bt)->
       let (oa, ka) = mmbinder_arities bt OConv in
       fn (mmsubst bt (Array.make oa OConv) (Array.make ka (KProd [])))

    | TVari(x)    -> assert false

  in fn t
