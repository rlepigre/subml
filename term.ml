(***************************************************************************)
(**{3                   Usefull fonction on terms                         }*)
(***************************************************************************)

open Ast
open Position
open Bindlib
open Format
open LibTools

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
