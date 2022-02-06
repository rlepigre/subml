(***************************************************************************)
(**{3                   Usefull fonction on terms                         }*)
(***************************************************************************)

open LibTools
open Ast
open Pos
open Bindlib

(** Test if a term is in normal form for CBV *)
let is_normal : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TAbst(_)
    | TCnst(_)
    | TAbrt         -> true

    | TFixY(_)
    | TAppl(_,_)
    | TCase(_,_,_)
    | TProj(_,_)
    | TPrnt(_)      -> false

    | TCoer(t,_)    -> fn t
    | TCons(_,a)    -> fn a
    | TDefi(d)      -> fn d.value
    | TReco(fs)     -> List.for_all (fun (_,t) -> fn t) fs

    | TMLet(_,_,bt) -> fn (mmsubst_dummy bt odummy kdummy)

    | TVari(_)
    | TVars(_)      -> assert false
  in fn t

(** Test if a term is neutral in CBV;
    This is not the exact definition of neutral.
    Here, we mean a term whose type in known
    with elimination or type decocation applied to it *)
let is_neutral : term -> bool = fun t ->
  let rec fn t =
    match t.elt with
    | TCoer(_,_)
    | TDefi(_)
    | TCnst(_)
    | TPrnt(_)     -> true

    | TAbrt
    | TCons(_,_)
    | TAbst(_)
    | TFixY(_)
    | TReco(_)     -> false

    | TAppl(a,_)
    | TProj(a,_)
    | TCase(a,_,_) -> fn a

    | TMLet(_,_,b) -> fn (mmsubst_dummy b odummy kdummy)

    | TVari(_)
    | TVars(_)     -> assert false

  in fn t
