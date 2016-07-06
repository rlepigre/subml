open Ast
open Bindlib

(****************************************************************************
 *                              Parser level AST                            *
 ****************************************************************************)

type pordinal = pordinal' position
and pordinal' =
  | PConv
  | PMaxi of pordinal list
  | PVari of string

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
  | PFixM of pordinal * string * pkind
  | PFixN of pordinal * string * pkind
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
  | PFixY of strpos * pterm

let list_nil _loc =
  in_pos _loc (PCons("Nil" , None))

let list_cons _loc t l =
  let c = in_pos _loc (PReco [("hd",t);("tl",l)]) in
  in_pos _loc (PCons("Cons", Some c))

let dummy_case_var _loc =
  (in_pos _loc "_", Some(dummy_pos (PProd [])))

(* "t; u" := "(fun (_ : unit) ↦ u) t" *)
let sequence _loc t u =
  let dum = (in_pos _loc "_", Some(in_pos _loc (PProd []))) in
  in_pos _loc (PAppl(in_pos _loc (PLAbs([dum],u)), t))

(****************************************************************************
 *                         Environment management                           *
 ****************************************************************************)

type env =
  { terms    : (string * tbox) list
  ; kinds    : (string * (kbox * (occur * int))) list
  ; ordinals : (string * obox) list }

let empty_env : env = { terms = [] ; kinds = [] ; ordinals = [] }

let add_term : string -> tbox -> env -> env = fun x t env ->
  { env with terms = (x,t) :: env.terms }

let add_kind : string -> kbox -> occur * int -> env -> env = fun x k o env ->
  { env with kinds = (x,(k,o)) :: env.kinds }

let add_ordinal : string -> obox -> env -> env = fun x o env ->
  { env with ordinals = (x,o) :: env.ordinals }

exception Unbound of strpos
let unbound s = raise (Unbound(s))

exception Arity_error of Location.t * string
let arity_error loc s = raise (Arity_error (loc,s))

exception Positivity_error of Location.t * string
let positivity_error loc s = raise (Positivity_error (loc,s))

(* Lookup a term variable in the environment. If it does not appear, look for
   the name in the list of term definitions. *)
let term_variable : env -> strpos -> tbox = fun env s ->
  try List.assoc s.elt env.terms with Not_found ->
  try
    let vd = Hashtbl.find val_env s.elt in
    tdefi s.pos vd
  with Not_found -> unbound s

(* Lookup an ordinal variable in the environment. *)
let ordinal_variable : env -> strpos -> obox = fun env s ->
  try List.assoc s.elt env.ordinals with Not_found -> unbound s

(* Lookup a kind variable in the environment. If it does not appear, look for
   the name in the list of type definitions. *)
let rec kind_variable : (occur * int) -> env -> strpos -> pkind array -> kbox =
 fun pos env s ks ->
  let arity = Array.length ks in
  try
    let (k, pos') = List.assoc s.elt env.kinds in
    if not (List.mem (fst (compose2 pos' pos)) [Non; Pos]) then
      let msg = Printf.sprintf "%s used in a negative position." s.elt in
      positivity_error s.pos msg
    else if arity > 0 then
      arity_error s.pos (s.elt ^ " does not expect arguments.")
    else k
  with Not_found ->
    try
      let td = Hashtbl.find typ_env s.elt in
      if td.tdef_arity <> arity then begin
        let msg =
          Printf.sprintf "%s expect %i arguments but received %i." s.elt
            td.tdef_arity (Array.length ks)
        in arity_error s.pos msg
      end;
      let ks = Array.mapi (fun i k ->
	unsugar_kind ~pos:(compose2 (td.tdef_variance.(i), td.tdef_depth.(i)) pos) env k) ks
      in
      kdefi td ks
    with Not_found -> unbound s

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

and unsugar_ordinal : env -> pordinal -> obox = fun env po ->
  match po.elt with
  | PConv   -> oconv
  | PVari s -> ordinal_variable env (in_pos po.pos s)
  | PMaxi l -> omaxi (List.map (unsugar_ordinal env) l)

and unsugar_kind : ?pos:(occur * int) -> env -> pkind -> kbox =
  fun ?(pos=(Pos,0)) (env:env) pk ->
  match pk.elt with
  | PFunc(a,b)   ->
     let (o,d) = pos in
     kfunc (unsugar_kind ~pos:(neg o, d+1) env a) (unsugar_kind ~pos:(o, d) env b)
  | PTVar(s,ks)  ->
     kind_variable pos env (in_pos pk.pos s) (Array.of_list ks)
  | PKAll(x,k)   -> let f xk =
                      unsugar_kind ~pos (add_kind x (box_of_var xk) (Non,-1) env) k
                    in kkall x f
  | PKExi(x,k)   -> let f xk =
                      unsugar_kind (add_kind x (box_of_var xk) (Non,-1) env) k
                    in kkexi x f
  | POAll(o,k)   -> let f xo =
                      unsugar_kind (add_ordinal o (box_of_var xo) env) k
                    in koall o f
  | POExi(o,k)   -> let f xo =
                      unsugar_kind (add_ordinal o (box_of_var xo) env) k
                    in koexi o f
  | PFixM(o,x,k) -> let o = unsugar_ordinal env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x (box_of_var xk) pos env) k
                    in kfixm x o f
  | PFixN(o,x,k) -> let o = unsugar_ordinal env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x (box_of_var xk) pos env) k
                    in kfixn x o f
  | PProd(fs)    -> let f (l,k) = (l, unsugar_kind ~pos env k) in
                    kprod (List.map f fs)
  | PDSum(cs)    -> let f (c,ko) =
                      match ko with
                      | None   -> (c, kprod [])
                      | Some k -> (c, unsugar_kind ~pos env k)
                    in kdsum (List.map f cs)
  | PDPrj(t,s)   -> kdprj (unsugar_term env t) s
  | PWith(a,s,b) -> kwith (unsugar_kind ~pos env a) s (unsugar_kind ~pos env b)

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
                         tabst pos ko x f
                   in aux true env vs
  | PKAbs(s,f)  -> let f xk =
                     unsugar_term (add_kind s.elt (box_of_var xk) (Non, -1) env) f
                   in tkabs s.pos s f
  | POAbs(s,f)  -> let f xo =
                      unsugar_term (add_ordinal s.elt (box_of_var xo) env) f
                   in toabs s.pos s f
  | PCoer(t,k)  -> tcoer pt.pos (unsugar_term env t) (unsugar_kind env k)
  | PAppl(t,u)  -> tappl pt.pos (unsugar_term env t) (unsugar_term env u)
  | PLVar(x)    -> term_variable env (in_pos pt.pos x)
  | PPrnt(s)    -> tprnt pt.pos s
  | PCons(c,uo) -> let u =
                     match uo with
                     | None   -> treco pt.pos []
                     | Some u -> unsugar_term env u
                   in tcons pt.pos c u
  | PProj(t,l)  -> tproj pt.pos (unsugar_term env t) l
  | PCase(t,cs) -> let f (c,x,t) =
                     let x = from_opt x (dummy_case_var t.pos) in
                     (c, unsugar_term env (in_pos t.pos (PLAbs([x],t))))
                   in tcase pt.pos (unsugar_term env t) (List.map f cs)
  | PReco(fs)   -> let f (l,t) = (l, unsugar_term env t) in
                   treco pt.pos (List.map f fs)
  | PFixY(x,t)  -> let f xt = unsugar_term (add_term x.elt (box_of_var xt) env) t in
                   tfixy pt.pos !(Typing.fixpoint_depth) x f
