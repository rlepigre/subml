open Pa_ocaml_prelude
open Decap
open Bindlib
open Util
open Ast
open Print

#define LOCATE locate

(* Some combinators. *)
let list_sep elt sep = parser
  | EMPTY                        -> []
  | e:elt es:{_:STR(sep) e:elt}* -> e::es

let list_sep' elt sep = parser
  | e:elt es:{_:STR(sep) e:elt}* -> e::es

let parser string_char =
  | "\\\"" -> "\""
  | "\\\\" -> "\\"
  | c:ANY  -> if c = '\\' || c = '"' || c = '\n' || c = '\r' then
                raise (Give_up "");
              String.make 1 c

let string_lit =
  let slit = parser "\"" cs:string_char* "\"" -> String.concat "" cs in
  change_layout slit no_blank

(* Keyword management. *)
let keywords = Hashtbl.create 20

let is_keyword : string -> bool = Hashtbl.mem keywords

let check_not_keyword : string -> unit = fun s ->
  if is_keyword s then
    raise (Give_up ("\""^s^"\" is a reserved identifier..."))

let new_keyword : string -> unit grammar = fun s ->
  let ls = String.length s in
  if ls < 1 then
    raise (Invalid_argument "invalid keyword");
  if Hashtbl.mem keywords s then
    raise (Invalid_argument "keyword already defied");
  Hashtbl.add keywords s s;
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to ls - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then
        raise (Give_up ("The keyword "^s^" was expected..."));
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' ->
        raise (Give_up ("The keyword "^s^" was expected..."))
    | _                                           -> ((), !str, !pos)
  in
  black_box f (Charset.singleton s.[0]) None s

(* Parser level AST. *)
type pkind = pkind' position
and pkind' =
  | PFunc of pkind * pkind
  | PTVar of string * pkind list
  | PFAll of string * pkind option * (orient * pkind list) option * pkind
  | PExis of string * pkind option * (orient * pkind list) option * pkind
  | PMu   of string * pkind
  | PNu   of string * pkind
  | PProd of (string * pkind) list
  | PSum  of (string * pkind option) list
  | PHole

type pterm = pterm' position
and pterm' =
  | PLAbs of (string position * pkind option) list * pterm
  | PCoer of pterm * pkind
  | PAppl of pterm * pterm
  | PLVar of string
  | PPrnt of string * pterm
  | PCstr of string * pterm option
  | PProj of pterm * string
  | PCase of pterm * (string * string * pterm) list * pterm option
  | PReco of (string * pterm) list

(* Basic tokens. *)
let case_kw = new_keyword "case"
let rec_kw  = new_keyword "rec"
let let_kw  = new_keyword "let"
let of_kw   = new_keyword "of"
let in_kw   = new_keyword "in"
let fix_kw  = new_keyword "fix"
let fun_kw  = new_keyword "fun"

let unfold_kw = new_keyword "unfold" 
let clear_kw  = new_keyword "clear" 
let parse_kw  = new_keyword "parse" 
let quit_kw   = new_keyword "quit" 
let exit_kw   = new_keyword "exit" 

let parser arrow  : unit grammar = "→" | "->"
let parser forall : unit grammar = "∀" | "/\\"
let parser exists : unit grammar = "∃" | "\\/"
let parser mu     : unit grammar = "μ" | "!"
let parser nu     : unit grammar = "ν" | "?"
let parser lambda : unit grammar = "λ" | fun_kw
let parser dot    : unit grammar = "." | "->" | "→"
let parser hole   : unit grammar = "?"

let parser ident = id:''[a-zA-Z][a-zA-Z0-9_']*'' -> check_not_keyword id; id

let parser orien = "<" -> LE | ">" -> GE

(****************************************************************************
 *                         A parser for kinds (types)                       *
 ****************************************************************************)

type pkind_prio = KFunc | KQuant | KAtom

let parser kind p =
  | a:(kind KQuant) arrow b:(kind KFunc) when p = KFunc
      -> in_pos _loc (PFunc(a,b))
  | id:ident l:{"(" l:kind_list ")"}?[[]] when p = KAtom
      -> in_pos _loc (PTVar(id,l))
  | forall id:ident ao:eq_kind? bnd:bounds? a:(kind KQuant) when p = KQuant
      -> in_pos _loc (PFAll(id,ao,bnd,a))
  | exists id:ident ao:eq_kind? bnd:bounds? a:(kind KQuant) when p = KQuant
      -> in_pos _loc (PExis(id,ao,bnd,a))
  | mu id:ident a:(kind KQuant) when p = KQuant
      -> in_pos _loc (PMu(id,a))
  | nu id:ident a:(kind KQuant) when p = KQuant
      -> in_pos _loc (PNu(id,a))
  | "{" fs:prod_items "}" when p = KAtom
      -> in_pos _loc (PProd(fs))
  | "[" fs:sum_items "]" when p = KAtom
      -> in_pos _loc (PSum(fs))
  | hole when p = KAtom
      -> in_pos _loc PHole

  | "(" a:(kind KFunc) ")"
  | a:(kind KQuant) when p = KFunc
  | a:(kind KAtom)  when p = KQuant

and kind_list = l:(list_sep (kind KFunc) ",")
and eq_kind   = "=" k:(kind KFunc)
and bounds    = o:orien l:kind_list ->
  if l = [] then raise (Give_up "At least one bound is required."); (o,l)
and sum_item  = id:ident a:{_:of_kw a:(kind KFunc)}?
and sum_items = l:(list_sep sum_item "|")
and prod_item  = id:ident ":" a:(kind KFunc)
and prod_items = l:(list_sep prod_item ";")

let kind = kind KFunc

let parser kind_def =
  | id:ident args:{"(" ids:(list_sep' ident ",") ")"}?[[]] "=" k:kind


(****************************************************************************
 *                          A parser for expressions                        *
 ****************************************************************************)

type pterm_prio = TFunc | TAppl | TColo | TAtom

let parser var =
  | id:ident                    -> (in_pos _loc_id id, None)
  | "(" id:ident ":" k:kind ")" -> (in_pos _loc_id id, Some k)

let parser term p =
  | lambda xs:var+ dot t:(term TFunc) when p = TFunc ->
      in_pos _loc (PLAbs(xs,t))
  | "(" t:(term TFunc) ":" k:kind when p = TAtom ->
      in_pos _loc (PCoer(t,k))
  | t:(term TAppl) u:(term TAtom) when p = TAppl ->
      in_pos _loc (PAppl(t,u))
  | id:ident when p = TAtom ->
      in_pos _loc (PLVar(id))
  | "print(" - s:string_lit - ")" ";" t:(term TColo) when p = TColo ->
      in_pos _loc (PPrnt(s,t))
  | c:ident "[" uo:(term TFunc)? "]" when p = TAtom ->
      in_pos _loc (PCstr(c,uo))
  | t:(term TAtom) "." l:ident when p = TAtom ->
      in_pos _loc (PProj(t,l))
  | case_kw t:(term TFunc) of_kw ps:pattern* w:wildcard? when p = TAtom ->
      in_pos _loc (PCase(t,ps,w))
  | "{" fs:field* "}" when p = TAtom ->
      in_pos _loc (PReco(fs))

  | "(" t:(term TAtom) ")"
  | t:(term TAtom) when p = TColo
  | t:(term TColo) when p = TAppl
  | t:(term TAppl) when p = TFunc

and pattern  = "|" c:ident "[" x:ident "]" _:arrow t:(term TFunc)
and wildcard = "|" "_" _:arrow t:(term TFunc)
and field    = l:ident "=" t:(term TFunc) ";"

let term = term TFunc

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

exception Unsugar_error of Location.t * string
let unsugar_error l s =
  raise (Unsugar_error (l,s))

let unsugar_kind : state -> (string * kbox) list -> pkind -> kbox =
  fun st env pk ->
  let tenv = st.tenv in
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
                let td = Hashtbl.find tenv s in
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
    | PFAll(x,ko,bnd,k) ->
        let f xk =
          let env = (x,xk) :: env in
          (unsugar_opt env ko, unsugar_bound env bnd, unsugar env k)
        in
        fall x f
    | PExis(x,ko,bnd,k) ->
        let f xk =
          let env = (x,xk) :: env in
          (unsugar_opt env ko, unsugar_bound env bnd, unsugar env k)
        in
        exis x f
    | PMu(x,k) ->
        fixm x (fun xk -> unsugar ((x,xk) :: env) k)
    | PNu(x,k) ->
        fixn x (fun xk -> unsugar ((x,xk) :: env) k)
    | PProd(fs)  ->
        prod (List.map (fun (l,k) -> (l, unsugar env k)) fs)
    | PSum(cs)   ->
        let cs = List.map (fun (c,ko) -> (c, unsugar_top env ko)) cs in
        let f x = func (prod (List.map (fun (c,k) -> (c,func k x)) cs)) x in
        fall' "XS" f
    | PHole      -> box (new_uvar ())
  and unsugar_opt env ko =
    match ko with
    | None   -> None
    | Some k -> Some (unsugar env k)
  and unsugar_bound env bnd =
    match bnd with
    | None        -> None
    | Some (o,ls) -> Some (o, List.map (unsugar env) ls)
  and unsugar_top env ko =
    match ko with
    | None   -> box top
    | Some k -> unsugar env k
  in unsugar env pk

let unsugar_term : state -> (string * tbox) list -> pterm -> tbox =
  fun st env pt ->
  let rec unsugar env pt =
    match pt.elt with
    | PLAbs(vs,t) ->
        let rec aux env = function
          | (x,ko)::xs ->
              let ko =
                match ko with
                | None   -> None
                | Some k -> Some (unsugar_kind st [] k)
              in
              let f xt = aux ((x.elt,xt)::env) xs in
              labs pt.pos ko x f
          | [] -> unsugar env t
        in
        aux env vs
    | PCoer(t,k) ->
        coer pt.pos (unsugar env t) (unsugar_kind st [] k)
    | PAppl(t,u) ->
        appl pt.pos (unsugar env t) (unsugar env u)
    | PLVar(x) ->
        begin
          try List.assoc x env with Not_found ->
          try
            let vd = Hashtbl.find st.venv x in
            vdef pt.pos vd
          with Not_found ->
            begin
              let msg = Printf.sprintf "Unboud variable %s." x in
              unsugar_error pt.pos msg
            end
        end
    | PPrnt(s,t) ->
        prnt pt.pos s (unsugar env t)
    | PCstr(c,uo) ->
        assert false (* TODO *)
    | PProj(t,l) ->
        proj pt.pos (unsugar env t) l
    | PCase(t,cs,wo) ->
        assert false (* TODO *)
    | PReco(fs) ->
        reco pt.pos (List.map (fun (l,t) -> (l, unsugar env t)) fs)
  in unsugar env pt

(****************************************************************************
 *                      High level parsing functions                        *
 ****************************************************************************)

exception Finish

let blank = blank_regexp ''[ \t\n\r]*''

let parser command =
  (* Type definition command. *)
  | type_kw (name,args,k):kind_def ->
      fun st ->
        let arg_names = Array.of_list args in
        let f args =
          let env = ref [] in
          Array.iteri (fun i k -> env := (arg_names.(i), k) :: !env) args;
          unsugar_kind st !env k
        in
        let b = mbind mk_free_tvar arg_names f in
        let td =
          { tdef_name  = name
          ; tdef_arity = Array.length arg_names
          ; tdef_value = unbox b }
        in
        Printf.fprintf stdout "%a\n%!" (print_kind_def false) td;
        Hashtbl.add st.tenv name td
  (* Unfold a type definition. *)
  | unfold_kw k:kind ->
      fun st ->
        let k = unbox (unsugar_kind st [] k) in
        Printf.fprintf stdout "%a\n%!" (print_kind true) k
  (* Clear the screen. *)
  | clear_kw ->
      fun _ -> ignore (Sys.command "clear")
  (* Parse a term. *)
  | parse_kw t:term ->
      fun st ->
        let t = unbox (unsugar_term st [] t) in
        Printf.fprintf stdout "%a\n%!" print_term t
  (* Exit the program. *)
  | {quit_kw | exit_kw} ->
      fun _ -> raise Finish

let command_of_string : state -> string -> unit = fun st s ->
  let parse = parse_string command blank in
  let action = Decap.handle_exception parse s in
  action st
