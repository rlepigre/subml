open Bindlib
open Format
open Ast
open Util

let rec print_list pelem sep ff = function
  | []    -> ()
  | [e]   -> pelem ff e
  | e::es -> fprintf ff "%a%s%a" pelem e sep (print_list pelem sep) es

let rec print_array pelem sep ff ls =
  print_list pelem sep ff (Array.to_list ls)

(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let rec print_kind wrap ff t =
  let pkind = print_kind false in
  let pkindw = print_kind true in
  match t with
  | TVar(x) ->
      pp_print_string ff (name_of x)
  | Func(a,b) ->
      if wrap then
        fprintf ff "(%a → %a)" pkindw a pkind b
      else
        fprintf ff "%a → %a" pkindw a pkind b
  | Prod(fs) ->
      let pfield ff (l,a) = fprintf ff "%s : %a" l pkind a in
      fprintf ff "{%a}" (print_list pfield "; ") fs
  | FAll(b) ->
      fprintf ff "∀%a" pquant b
  | Exis(b) ->
      fprintf ff "∃%a" pquant b
  | TDef(td,args) ->
      if Array.length args = 0 then
        pp_print_string ff td.tdef_name
      else
        fprintf ff "%s(%a)" td.tdef_name (print_array pkind ", ") args
  | TCst(_) ->
      fprintf ff "ε(...)"
  | UVar(v) ->
      begin
        match v.uvar_val with
        | None   -> fprintf ff "?%i" v.uvar_key
        | Some a -> print_kind wrap ff a
      end

and pquant ff b =
  let x = new_tvar (binder_name b) in
  let (ao, bnd, c) = subst b (free_of x) in
  pp_print_string ff (name_of x);
  let pkind = print_kind true in
  let pklist = print_list pkind ", " in
  match (ao, bnd) with
  | (None  , None       ) -> fprintf ff " %a" pkind c
  | (Some a, None       ) -> fprintf ff " = %a %a" pkind a pkind c
  | (None  , Some (o,ls)) ->
      let o = match o with GE -> ">" | LE -> "<" in
      fprintf ff " %s %a %a" o pklist ls pkind c
  | (Some a, Some (o,ls)) ->
      let o = match o with GE -> ">" | LE -> "<" in
      fprintf ff " = %a %s %a %a" pkind a o pklist ls pkind c

(****************************************************************************
 *                           Printing of a term                             *
 ****************************************************************************)

let rec print_term ff t =
  let pkind = print_kind false in
  match t.elt with
  | Coer(t,a) ->
      fprintf ff "(%a : %a)" print_term t pkind a
  | LVar(x) ->
      pp_print_string ff (name_of x)
  | LAbs(ao,b) ->
      let x = binder_name b in
      let t = subst b (free_of (new_lvar' x)) in
      begin
        match ao with
        | None   -> fprintf ff "λ%s %a" x print_term t
        | Some a -> fprintf ff "λ%s : %a %a" x pkind a print_term t
      end
  | Appl(t,u) ->
      fprintf ff "(%a) %a" print_term t print_term u
  | Reco(fs) ->
      let pfield ff (l,t) = fprintf ff "%s = %a" l print_term t in
      fprintf ff "{%a}" (print_list pfield "; ") fs
  | Proj(t,l) ->
      fprintf ff "%a.%s" print_term t l
  | VDef(v) ->
      pp_print_string ff v.name
  | Prnt(s,t) ->
      fprintf ff "print(%S); %a" s print_term t
  | FixY ->
      pp_print_string ff "fix"
  | Cnst(_) ->
      pp_print_string ff "ε(...)"

(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let print_term ch t =
  let ff = formatter_of_out_channel ch in
  print_term ff t; pp_print_flush ff (); flush ch

let print_kind ch t =
  let ff = formatter_of_out_channel ch in
  print_kind false ff t; pp_print_flush ff (); flush ch
