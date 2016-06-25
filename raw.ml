open Util
open Ast
open Bindlib

(****************************************************************************
 *                              Parser level AST                            *
 ****************************************************************************)

type pkind = pkind' position
and pkind' =
  | PTVar of string * pkind list
  | PFunc of pkind * pkind
  | PProd of (string * pkind) list
  | PDSum of (string * pkind option) list
  | PKAll of string * pkind
  | PKExi of string * pkind
  | POAll of string * pkind
  | POExi of string * pkind
  | PFixM of string option * string * pkind
  | PFixN of string option * string * pkind
  | PDPrj of pterm  * string
  | PWith of pkind * string * pkind

and pterm  = pterm' position
and pterm' =
  | PCoer of pterm * pkind
  | PLVar of string
  | PLAbs of (strpos * pkind option) list * pterm
  | PAppl of pterm * pterm
  | PReco of (string * pterm) list
  | PProj of pterm * string
  | PCons of string * pterm option
  | PCase of pterm * (string * (strpos * pkind option) option * pterm) list
  | PKAbs of strpos * pterm
  | PPrnt of string
  | PFixY of (strpos * pkind option) * pterm

let list_nil _loc =
  in_pos _loc (PCons("Nil" , None))

let list_cons _loc t l =
  let c = in_pos _loc (PReco [("hd",t);("tl",l)]) in
  in_pos _loc (PCons("Cons", Some c))

let dummy_case_var _loc =
  (in_pos _loc "_", Some(dummy_pos (PProd [])))

(****************************************************************************
 *                         Environment management                           *
 ****************************************************************************)

type env =
  { terms : (string * tbox) list
  ; kinds : (string * kbox) list }

let empty_env : env = { terms = [] ; kinds = [] }

let find_term : string -> env -> tbox = fun s env ->
  List.assoc s env.terms

let find_kind : string -> env -> kbox = fun s env ->
  List.assoc s env.kinds

let add_term : string -> tbox -> env -> env = fun x t env ->
  { env with terms = (x,t) :: env.terms }

let add_kind : string -> kbox -> env -> env = fun x k env ->
  { env with kinds = (x,k) :: env.kinds }

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

exception Unbound of strpos
let unbound s = raise (Unbound(s))

exception Unsugar_error of Location.t * string
let unsugar_error loc s = raise (Unsugar_error (loc,s))

let kind_variable : env -> strpos -> kbox array -> kbox = fun env s ks ->
  let arity = Array.length ks in
  try
    let k = find_kind s.elt env in
    if arity > 0 then
      unsugar_error s.pos (s.elt ^ " does not expect arguments.")
    else k
  with Not_found ->
    try
      let td = Hashtbl.find typ_env s.elt in
      if td.tdef_arity <> arity then
        let msg =
          Printf.sprintf "%s expect %i arguments but received %i." s.elt
            td.tdef_arity (Array.length ks)
        in unsugar_error s.pos msg
      else tdef td ks
    with Not_found -> unbound s

let term_variable : env -> strpos -> tbox = fun env s ->
  try find_term s.elt env with Not_found ->
  try
    let vd = Hashtbl.find val_env s.elt in
    vdef s.pos vd
  with Not_found -> unbound s

let rec unsugar_kind : env -> pkind -> kbox = fun env pk ->
  match pk.elt with
  | PFunc(a,b)   -> func (unsugar_kind env a) (unsugar_kind env b)
  | PTVar(s,ks)  -> let ks = Array.of_list (List.map (unsugar_kind env) ks) in
                    kind_variable env (in_pos pk.pos s) ks
  | PKAll(x,k)   -> let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in kall x f
  | PKExi(x,k)   -> let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in kexi x f
  | POAll(o,k)   -> assert false (* TODO *)
  | POExi(o,k)   -> assert false (* TODO *)
  | PFixM(_,x,k) -> let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in fixm x f
  | PFixN(_,x,k) -> let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in fixn x f
  | PProd(fs)    -> let f (l,k) = (l, unsugar_kind env k) in
                    prod (List.map f fs)
  | PDSum(cs)    -> let f (c,ko) =
                      match ko with
                      | None   -> (c, prod [])
                      | Some k -> (c, unsugar_kind env k)
                    in dsum (List.map f cs)
  | PDPrj(t,s)   -> dprj (unsugar_term env t) s
  | PWith(a,s,b) -> wIth (unsugar_kind env a) s (unsugar_kind env b)

and unsugar_term : env -> pterm -> tbox = fun env pt ->
  match pt.elt with
  | PLAbs(vs,t) -> let rec aux first env = function
                     | []           -> unsugar_term env t
                     | (x,ko) :: xs ->
                         let ko = map_opt (unsugar_kind env) ko in
                         let f xt = aux false (add_term x.elt xt env) xs in
                         let pos =
                           if first then pt.pos else
                           Location.({ pt.pos with loc_start = x.pos.loc_start })
                         in
                         labs pos ko x f
                   in aux true env vs
  | PKAbs(s,f)  -> let f xk = unsugar_term (add_kind s.elt xk env) f in
                   kabs s.pos s f
  | PCoer(t,k)  -> coer pt.pos (unsugar_term env t) (unsugar_kind env k)
  | PAppl(t,u)  -> appl pt.pos (unsugar_term env t) (unsugar_term env u)
  | PLVar(x)    -> term_variable env (in_pos pt.pos x)
  | PPrnt(s)    -> prnt pt.pos s
  | PCons(c,uo) -> let u =
                     match uo with
                     | None   -> reco pt.pos []
                     | Some u -> unsugar_term env u
                   in cons pt.pos c u
  | PProj(t,l)  -> proj pt.pos (unsugar_term env t) l
  | PCase(t,cs) -> let f (c,x,t) =
                     let x = from_opt x (dummy_case_var t.pos) in
                     (c, unsugar_term env (in_pos t.pos (PLAbs([x],t))))
                   in case pt.pos (unsugar_term env t) (List.map f cs)
  | PReco(fs)   -> let f (l,t) = (l, unsugar_term env t) in
                   reco pt.pos (List.map f fs)
  | PFixY(x,t)  -> let (x, ko) = x in
                   let ko = map_opt (unsugar_kind env) ko in
                   let f xt = unsugar_term (add_term x.elt xt env) t in
                   fixy pt.pos ko x f
