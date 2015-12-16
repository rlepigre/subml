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

(* ordinals in this list are not printed *)
let ignored_ordinals = ref []

(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let print_ordinal ff o =
  let rec print_ordinal ff = function
    | ODumm        -> pp_print_string ff "?"
    | OConv        -> pp_print_string ff "∞"
    | OLess(o,t,k) -> if List.memq o !ignored_ordinals then print_ordinal ff o
                      else fprintf ff "ε(< %a)" print_ordinal o
    | OLEqu(o,t,k) -> if List.memq o !ignored_ordinals then print_ordinal ff o
	              else fprintf ff "ε(≤ %a)" print_ordinal o
    | OTag i       -> fprintf ff "?%i" i
  in
  match o with
  | OConv -> ()
  | _     -> print_ordinal ff o

let rec print_kind unfold wrap ff t =
  let pkind = print_kind unfold false in
  let pkindw = print_kind unfold true in
  match repr t with
  | TVar(x) ->
      pp_print_string ff (name_of x)
  | Func(a,b) ->
      if wrap then pp_print_string ff "(";
      fprintf ff "%a → %a" pkindw a pkind b;
      if wrap then pp_print_string ff ")"
  | Prod(fs) ->
      let pfield ff (l,a) = fprintf ff "%s : %a" l pkind a in
      fprintf ff "{%a}" (print_list pfield "; ") fs
  | DSum(cs) ->
      let pvariant ff (c,a) = fprintf ff "%s of %a" c pkind a in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
  | FAll(f)  ->
      let x = new_tvar (binder_name f) in
      fprintf ff "∀%s %a" (name_of x) pkind (subst f (free_of x))
  | Exis(f)  ->
      let x = new_tvar (binder_name f) in
      fprintf ff "∀%s %a" (name_of x) pkind (subst f (free_of x))
  | FixM(o,b) ->
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "μ%a%s %a" print_ordinal o (name_of x) pkindw a
  | FixN(o,b) ->
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "ν%a%s %a" print_ordinal o (name_of x) pkindw a
  | TDef(td,args) ->
      if unfold then
        print_kind unfold wrap ff (msubst td.tdef_value args)
      else
        if Array.length args = 0 then
          pp_print_string ff td.tdef_name
        else
          fprintf ff "%s(%a)" td.tdef_name (print_array pkind ", ") args
  | UCst(_) ->
      pp_print_string ff "ε∀"
  | ECst(_) ->
      pp_print_string ff "ε∃"
  | UVar(u) ->
      fprintf ff "?%i" u.uvar_key
  | TInt(_) -> assert false

let pkind_def unfold ff kd =
  pp_print_string ff kd.tdef_name;
  let names = mbinder_names kd.tdef_value in
  let xs = new_mvar mk_free_tvar names in
  let k = msubst kd.tdef_value (Array.map free_of xs) in
  if Array.length names > 0 then
    fprintf ff "(%a)" (print_array pp_print_string ",") names;
  fprintf ff " = %a" (print_kind unfold false) k


(****************************************************************************
 *                           Printing of a term                             *
 ****************************************************************************)

let rec print_term ff t =
  let pkind = print_kind false false in
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
        | Some a -> fprintf ff "λ(%s : %a) %a" x pkind a print_term t
      end
  | Appl(t,u) ->
      fprintf ff "(%a) %a" print_term t print_term u
  | Reco(fs) ->
      let pfield ff (l,t) = fprintf ff "%s = %a" l print_term t in
      fprintf ff "{%a}" (print_list pfield "; ") fs
  | Proj(t,l) ->
      fprintf ff "%a.%s" print_term t l
  | Cons(c,t) ->
     (match t.elt with
     | Reco([]) -> fprintf ff "%s" c
     | _ -> fprintf ff "%s %a" c print_term t)
  | Case(t,l) ->
     let pvariant ff (c,b) =
       match b.elt with
       | LAbs(_,f) ->
           let x = binder_name f in
           let t = subst f (free_of (new_lvar' x)) in
           fprintf ff "| %s[%s] → %a" c x print_term t
       | _ ->
           fprintf ff "| %s → %a" c print_term b
      in
      fprintf ff "case %a of %a" print_term t (print_list pvariant "; ") l
  | VDef(v) ->
      pp_print_string ff v.name
  | Prnt(s) ->
      fprintf ff "print(%S)" s
  | FixY(t) ->
      fprintf ff "fix %a" print_term t
  | Cnst(_) ->
      pp_print_string ff "ε"
  | TagI(i) ->
      fprintf ff "TAG(%i)" i

(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let print_term ch t =
  let ff = formatter_of_out_channel ch in
  print_term ff t; pp_print_flush ff (); flush ch

let print_kind unfold ch t =
  let ff = formatter_of_out_channel ch in
  print_kind unfold false ff t; pp_print_flush ff (); flush ch

let print_kind_def unfold ch kd =
  let ff = formatter_of_out_channel ch in
  pkind_def unfold ff kd; pp_print_flush ff (); flush ch
