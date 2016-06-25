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
  (*
  | POAll of string * pkind
  | POExi of string * pkind
  *)
  | PFixM of string * pkind
  | PFixN of string * pkind
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

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

exception Unbound of Location.t * string
let unbound loc s = raise (Unbound(loc,s))

exception Unsugar_error of Location.t * string
let unsugar_error loc s = raise (Unsugar_error (loc,s))

let rec unsugar_kind : (string * tbox) list -> (string * kbox) list -> pkind -> kbox =
  fun lenv env pk ->
  let rec unsugar env pk =
    match pk.elt with
    | PFunc(a,b) ->
        func (unsugar env a) (unsugar env b)
    | PTVar(s,ks) ->
        begin
          try
            let k = List.assoc s env in
            if ks <> [] then
                let msg = Printf.sprintf "%s does note expect arguments." s in
                unsugar_error pk.pos msg
            else k
          with Not_found ->
            let ks = Array.of_list ks in
            try
              let ks = Array.map (unsugar env) ks in
              let td = Hashtbl.find typ_env s in
              if td.tdef_arity <> Array.length ks then
                begin
                  let msg =
                    Printf.sprintf
                      "%s expect %i arguments but received %i." s
                      td.tdef_arity (Array.length ks)
                  in
                  unsugar_error pk.pos msg
                end;
              tdef td ks
            with Not_found -> unbound pk.pos s
        end
    | PKAll(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       kall x f
    | PKExi(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       kexi x f
    | PFixM(x,k) ->
       fixm x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PFixN(x,k) ->
       fixn x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PProd(fs)  ->
       prod (List.map (fun (l,k) -> (l, unsugar env k)) fs)
    | PDSum(cs)   ->
       dsum (List.map (fun (c,k) -> (c, unsugar_top env k)) cs)
    | PDPrj(t,s) ->
       dprj (unsugar_term lenv env t) s
    | PWith(a,s,b) ->
       wIth (unsugar env a) s (unsugar env b)
  and unsugar_top env ko =
    match ko with
    | None   -> prod []
    | Some k -> unsugar env k
  in unsugar env pk

and unsugar_term : (string * tbox) list -> (string * kbox) list -> pterm -> tbox =
  fun lenv kenv pt ->
  let rec unsugar pt =
    match pt.elt with
    | PLAbs(vs,t) ->
        let rec aux first lenv = function
          | (x,ko)::xs ->
              let ko =
                match ko with
                | None   -> None
                | Some k -> Some (unsugar_kind lenv kenv k)
              in
              let f xt = aux false ((x.elt,xt)::lenv) xs in
              let pos = if first then pt.pos else
                  Location.({ pt.pos with loc_start = x.pos.loc_start })
              in
              labs pos ko x f
          | [] -> unsugar_term lenv kenv t
        in
        aux true lenv vs
    | PKAbs(s,f) ->
       let f xk = unsugar_term lenv ((s.elt,xk) :: kenv) f in
       kabs s.pos s f
    | PCoer(t,k) ->
        coer pt.pos (unsugar t) (unsugar_kind lenv kenv k)
    | PAppl(t,u) ->
        appl pt.pos (unsugar t) (unsugar u)
    | PLVar(x) ->
        begin
          try List.assoc x lenv with Not_found ->
          try
            let vd = Hashtbl.find val_env x in
            vdef pt.pos vd
          with Not_found -> unbound pt.pos x
        end
    | PPrnt(s) ->
        prnt pt.pos s
    | PCons(c,uo) ->
        let u =
          match uo with
          | None   -> reco dummy_position []
          | Some u -> unsugar u
        in
        cons pt.pos c u
    | PProj(t,l) ->
        proj pt.pos (unsugar t) l
    | PCase(t,cs) ->
       let f (c,x,t) =
         (c, unsugar (match x with
         | None   -> dummy_pos (PLAbs([dummy_pos "_", Some(dummy_pos (PProd([])))], t))
         | Some x -> dummy_pos (PLAbs([x],t))))
        in
        case pt.pos (unsugar t) (List.map f cs)
    | PReco(fs) ->
        reco pt.pos (List.map (fun (l,t) -> (l, unsugar t)) fs)
    | PFixY((x,ko),t) ->
       let ko =
         match ko with
         | None   -> None
         | Some k -> Some (unsugar_kind lenv kenv k)
       in
       let f xt = unsugar_term ((x.elt,xt)::lenv) kenv t in
       fixy pt.pos ko x f
  in
  unsugar pt
