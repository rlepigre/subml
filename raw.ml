open Util
open Ast
open Bindlib

(* Parser level AST. *)
type pkind = pkind' position
and pkind' =
  | PFunc of pkind * pkind
  | PTVar of string * pkind list
  | PFAll of string * pkind
  | PExis of string * pkind
  | PMu   of string * pkind
  | PNu   of string * pkind
  | PDPrj of pterm  * string
  | PWith of pkind * string * pkind
  | PWhen of pkind * pkind * pkind
  | PProd of (string * pkind) list
  | PSum  of (string * pkind option) list
  | PHole

and pterm = pterm' position
and pterm' =
  | PLAbs of (strpos * pkind option) list * pterm
  | PKAbs of strpos * pterm
  | PCoer of pterm * pkind
  | PAppl of pterm * pterm
  | PLVar of string
  | PPrnt of string
  | PCstr of string * pterm option
  | PProj of pterm * string
  | PCase of pterm * (string * (strpos * pkind option) option * pterm) list
  | PReco of (string * pterm) list
  | PFixY of (strpos * pkind option) * pterm

let list_nil _loc =
  in_pos _loc (PCstr("Nil" , None))

let list_cons _loc t l =
  in_pos _loc (PCstr("Cons", Some (in_pos _loc (PReco [("hd",t);("tl",l)]))))

exception Unbound of Location.t * string

let unbound loc s = raise (Unbound(loc,s))

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

exception Unsugar_error of Location.t * string
let unsugar_error l s =
  raise (Unsugar_error (l,s))

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
    | PFAll(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       kall x f
    | PExis(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       kexi x f
    | PMu(x,k) ->
       fixm x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PNu(x,k) ->
       fixn x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PProd(fs)  ->
       prod (List.map (fun (l,k) -> (l, unsugar env k)) fs)
    | PSum(cs)   ->
       dsum (List.map (fun (c,k) -> (c, unsugar_top env k)) cs)
    | PDPrj(t,s) ->
       dprj (unsugar_term lenv env t) s
    | PWith(a,s,b) ->
       wIth (unsugar env a) s (unsugar env b)
    | PWhen(a,b,c) ->
       wHen (unsugar env a) (unsugar env b) (unsugar env c)
    | PHole      -> box (new_uvar ())
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
    | PCstr(c,uo) ->
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
