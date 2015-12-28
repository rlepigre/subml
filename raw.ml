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
  | PProd of (string * pkind) list
  | PSum  of (string * pkind option) list
  | PHole

type pterm = pterm' position
and pterm' =
  | PLAbs of (strpos * pkind option) list * pterm
  | PCoer of pterm * pkind
  | PAppl of pterm * pterm
  | PLVar of string
  | PPrnt of string
  | PCstr of string * pterm option
  | PProj of pterm * string
  | PCase of pterm * (string * (strpos * pkind option) option * pterm) list
  | PReco of (string * pterm) list
  | PFixY of (strpos * pkind option) * pterm

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

exception Unsugar_error of Location.t * string
let unsugar_error l s =
  raise (Unsugar_error (l,s))

let unsugar_kind : (string * kbox) list -> pkind -> kbox =
  fun env pk ->
  let rec unsugar env pk =
    match pk.elt with
    | PFunc(a,b) ->
        func (unsugar env a) (unsugar env b)
    | PTVar(s,ks) ->
        begin
          try
            let k = List.assoc s env in
            if ks <> [] then
              begin
                let msg = Printf.sprintf "%s does note expect arguments." s in
                unsugar_error pk.pos msg
              end
            else k
          with Not_found ->
            begin
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
              with Not_found ->
                begin
                  let msg = Printf.sprintf "Unboud variable %s." s in
                  unsugar_error pk.pos msg
                end
            end
        end
    | PFAll(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       fall x f
    | PExis(x,k) ->
       let f xk = unsugar ((x,box_of_var xk) :: env) k in
       exis x f
    | PMu(x,k) ->
       fixm x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PNu(x,k) ->
       fixn x (fun xk -> unsugar ((x,box_of_var xk) :: env) k)
    | PProd(fs)  ->
       prod (List.map (fun (l,k) -> (l, unsugar env k)) fs)
    | PSum(cs)   ->
       dsum (List.map (fun (c,k) -> (c, unsugar_top env k)) cs)
    | PHole      -> box (new_uvar ())
  and unsugar_top env ko =
    match ko with
    | None   -> prod []
    | Some k -> unsugar env k
  in unsugar env pk

let unsugar_term : (string * tbox) list -> pterm ->
                   tbox * (string * (term variable * pos list)) list =
  fun env pt ->
  let unbound = ref [] in
  let rec unsugar env pt =
    match pt.elt with
    | PLAbs(vs,t) ->
        let rec aux env = function
          | (x,ko)::xs ->
              let ko =
                match ko with
                | None   -> None
                | Some k -> Some (unsugar_kind [] k)
              in
              let f xt = aux ((x.elt,xt)::env) xs in
              labs pt.pos ko x f
          | [] -> unsugar env t
        in
        aux env vs
    | PCoer(t,k) ->
        coer pt.pos (unsugar env t) (unsugar_kind [] k)
    | PAppl(t,u) ->
        appl pt.pos (unsugar env t) (unsugar env u)
    | PLVar(x) ->
        begin
          try List.assoc x env with Not_found ->
          try
            let vd = Hashtbl.find val_env x in
            vdef pt.pos vd
          with Not_found ->
            begin
              try
                let (v, ps) = List.assoc x !unbound in
                unbound := List.remove_assoc x !unbound;
                unbound := (x, (v, pt.pos :: ps)) :: !unbound;
                lvar pt.pos v
              with Not_found ->
                begin
                  let v = new_lvar' x in
                  unbound := (x, (v, [pt.pos])) :: !unbound;
                  lvar pt.pos v
                end
            end
        end
    | PPrnt(s) ->
        prnt pt.pos s
    | PCstr(c,uo) ->
        let u =
          match uo with
          | None   -> reco dummy_position []
          | Some u -> unsugar env u
        in
        cons pt.pos c u
    | PProj(t,l) ->
        proj pt.pos (unsugar env t) l
    | PCase(t,cs) ->
       let f (c,x,t) =
	 (c, unsugar env (match x with
	 | None   -> dummy_pos (PLAbs([dummy_pos "_", Some(dummy_pos (PProd([])))], t))
	 | Some x -> dummy_pos (PLAbs([x],t))))
        in
        case pt.pos (unsugar env t) (List.map f cs)
    | PReco(fs) ->
        reco pt.pos (List.map (fun (l,t) -> (l, unsugar env t)) fs)
    | PFixY((x,ko),t) ->
       let ko =
         match ko with
         | None   -> None
         | Some k -> Some (unsugar_kind [] k)
       in
       let f xt = unsugar ((x.elt,xt)::env) t in
       fixy pt.pos ko x f
  in
  let t = unsugar env pt in
  (t, !unbound)
