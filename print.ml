open Bindlib
open Format
open Ast
open Util

let rec print_list pelem sep ff = function
  | []    -> ()
  | [e]   -> pelem ff e
  | e::es -> fprintf ff "%a%s%a" pelem e sep (print_list pelem sep) es

(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let rec print_kind br ff = function
  | TVar(x)           ->
      fprintf ff "%s" (name_of x)
  | Func(a,b) when br ->
      fprintf ff "(%a → %a)" (print_kind br) a (print_kind br) b
  | Func(a,b)         ->
      fprintf ff "%a → %a" (print_kind br) a (print_kind br) b
  | Prod(a,l,b)       ->
      fprintf ff "{%a ; l = %a}" (print_kind br) a (print_kind br) b
  | Unit              ->
      fprintf ff "{}"
  | FAll(bo,b)        ->
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "∀ %a, %a" (print_bounds x) bo (print_kind true) a
  | Exis(bo,b)        ->
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "∃ %a, %a" (print_bounds x) bo (print_kind true) a
  | TDef(td,[||])      ->
      fprintf ff "%s" td.tdef_name
  | TDef(td,args)      ->
      let ls = Array.to_list args in
      fprintf ff "%s[%a]" td.tdef_name (print_list (print_kind false) ", ") ls
  | TCst(c)            ->
      fprintf ff "ε(...)"
  | UVar(v)            ->
      begin
        match v.uvar_val with
        | None   -> fprintf ff "?%i" v.uvar_key
        | Some a -> print_kind br ff a
      end

and print_bounds x ff = function
  | None        ->
      fprintf ff "%s" (name_of x)
  | Some(o,bs) ->
      let nx = name_of x in
      let o = match o with GE -> ">" | LE -> "<" in
      let bs = List.map (fun b -> subst b (free_of x)) bs in
      fprintf ff "%s %s %a" nx o (print_list (print_kind false) ", ") bs

let print_kind = print_kind false

(****************************************************************************
 *                           Printing of a term                             *
 ****************************************************************************)

let rec print_term ff t = match t.elt with
  | Coer(t,a)       ->
      fprintf ff "%a : %a" print_term t print_kind a
  | TAbs(b)         ->
      let x = new_tvar (binder_name b) in
      let t = subst b (free_of x) in
      fprintf ff "Λ %s.%a" (name_of x) print_term t
  | LVar(x)         ->
      fprintf ff "%s" (name_of x)
  | LAbs(None,b)    ->
      let x = binder_name b in
      let t = subst b (free_of (new_lvar' x)) in
      fprintf ff "λ%s %a" x print_term t
  | LAbs(Some(a),b) ->
      let x = binder_name b in
      let t = subst b (free_of (new_lvar' x)) in
      fprintf ff "λ%s : %a %a" x print_kind a print_term t
  | Appl(t,u)       ->
      fprintf ff "(%a) %a" print_term t print_term u
  | LLet(r,ns,b)    ->
      assert false (* TODO *)
  | Reco(td,l,t)    ->
      fprintf ff "{%a; %s = %a}" print_term td l print_term t
  | URec            ->
      fprintf ff "{}"
  | Proj(t,l)       ->
      fprintf ff "%a.%s" print_term t l
  | VDef(v)         ->
      fprintf ff "%s" v.name
  | Prnt(s,t)       ->
      fprintf ff "print(%s); %a" s print_term t
  | Cnst(c)         ->
      assert false (* TODO *)
