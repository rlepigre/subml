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
  | POAbs of strpos * pterm
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
  { terms    : (string * tbox) list
  ; kinds    : (string * kbox) list
  ; ordinals : (string * obox) list }

let empty_env : env = { terms = [] ; kinds = [] ; ordinals = [] }

let add_term : string -> tbox -> env -> env = fun x t env ->
  { env with terms = (x,t) :: env.terms }

let add_kind : string -> kbox -> env -> env = fun x k env ->
  { env with kinds = (x,k) :: env.kinds }

let add_ordinal : string -> obox -> env -> env = fun x o env ->
  { env with ordinals = (x,o) :: env.ordinals }

exception Unbound of strpos
let unbound s = raise (Unbound(s))

exception Arity_error of Location.t * string
let arity_error loc s = raise (Arity_error (loc,s))


(* Lookup a kind variable in the environment. If it does not appear, look for
   the name in the list of type definitions. *)
let kind_variable : env -> strpos -> kbox array -> kbox = fun env s ks ->
  let arity = Array.length ks in
  try
    let k = List.assoc s.elt env.kinds in
    if arity > 0 then
      arity_error s.pos (s.elt ^ " does not expect arguments.")
    else k
  with Not_found ->
    try
      let td = Hashtbl.find typ_env s.elt in
      if td.tdef_arity <> arity then
        let msg =
          Printf.sprintf "%s expect %i arguments but received %i." s.elt
            td.tdef_arity (Array.length ks)
        in arity_error s.pos msg
      else tdef td ks
    with Not_found -> unbound s

(* Lookup a term variable in the environment. If it does not appear, look for
   the name in the list of term definitions. *)
let term_variable : env -> strpos -> tbox = fun env s ->
  try List.assoc s.elt env.terms with Not_found ->
  try
    let vd = Hashtbl.find val_env s.elt in
    vdef s.pos vd
  with Not_found -> unbound s

(* Lookup an ordinal variable in the environment. *)
let ordinal_variable : env -> strpos -> obox = fun env s ->
  try List.assoc s.elt env.ordinals with Not_found -> unbound s

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

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
  | POAll(o,k)   -> let f xo =
                      unsugar_kind (add_ordinal o (box_of_var xo) env) k
                    in oall o f
  | POExi(o,k)   -> let f xo =
                      unsugar_kind (add_ordinal o (box_of_var xo) env) k
                    in oexi o f
  | PFixM(o,x,k) -> let o =
                      match o with
                      | None   -> box OConv
                      | Some o -> ordinal_variable env (in_pos pk.pos o)
                    in
                    let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in fixm x o f
  | PFixN(o,x,k) -> let o =
                      match o with
                      | None   -> box OConv
                      | Some o -> ordinal_variable env (in_pos pk.pos o)
                    in
                    let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) env) k
                    in fixn x o f
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
                         let f xt = aux false (add_term x.elt (box_of_var xt) env) xs in
                         let pos =
                           if first then pt.pos else
                           let open Location in
                           { pt.pos with loc_start = x.pos.loc_start }
                         in
                         labs pos ko x f
                   in aux true env vs
  | PKAbs(s,f)  -> let f xk =
                     unsugar_term (add_kind s.elt (box_of_var xk) env) f
                   in kabs s.pos s f
  | POAbs(s,f)  -> let f xo =
                      unsugar_term (add_ordinal s.elt (box_of_var xo) env) f
                   in oabs s.pos s f
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
                   let f xt = unsugar_term (add_term x.elt (box_of_var xt) env) t in
                   fixy pt.pos ko x f
