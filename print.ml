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

(* ordinals in this list are not printed, used
   to remove unused induction rule from printing *)
let ignored_ordinals = ref []

let rec onorm o =
  match o with
  | OLess(o',t,k) when List.memq o !ignored_ordinals -> onorm o'
  | OLEqu(o',t,k) when List.memq o !ignored_ordinals -> onorm o'
  | _ -> o


(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let ordinal_tbl = ref []
let ordinal_count = ref 0

let rec print_ordinal unfold ff o =
  let o = onorm o in
  match o with
  | ODumm        -> pp_print_string ff "?"
  | OConv        -> pp_print_string ff "∞"
  | OTag i       -> fprintf ff "?%i" i
  | _ ->
  if unfold then match o with
  | OLess(o,t,k) ->
    fprintf ff "ε(< %a, %a in %a)" (print_ordinal false) o (print_term unfold) t print_ord_cstr k
  | OLEqu(o,t,k) ->
    fprintf ff "ε(≤ %a, %a in %a)" (print_ordinal false) o (print_term unfold) t print_ord_cstr k
  | _ -> assert false
  else
    let n =
      try
	List.assq o !ordinal_tbl
      with
	Not_found ->
	  let n = !ordinal_count in incr ordinal_count;
	  ordinal_tbl := (o,n)::!ordinal_tbl; n
    in
    fprintf ff "ε%d" n

and print_reset_ordinals ff =
  while !ordinal_tbl <> [] do
    let (o,n) = match !ordinal_tbl with
      | [] -> assert false
      | x::os -> ordinal_tbl := os; x
    in
    fprintf ff "  ε%d = %a\n%!" n (print_ordinal true) o
  done;
  ordinal_count := 0

and print_ord_cstr ff k =
  match k with
  | In k -> fprintf ff "∈ %a" (print_kind false false) (subst k ODumm)
  | NotIn k -> fprintf ff "∉ %a" (print_kind false false) (subst k ODumm)

and print_index_ordinal ff = function
  | OConv -> ()
  | o -> fprintf ff "[%a]" (print_ordinal false) o

and print_kind unfold wrap ff t =
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
      fprintf ff "μ%a%s %a" print_index_ordinal o (name_of x) pkindw a
  | FixN(o,b) ->
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "ν%a%s %a" print_index_ordinal o (name_of x) pkindw a
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
  | TInt(n) ->
      fprintf ff "!%i" n

and pkind_def unfold ff kd =
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

and print_term unfold ff t =
  let print_term = print_term unfold in
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
     if unfold then
       print_term ff v.value
     else
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

let print_term unfold ch t =
  let ff = formatter_of_out_channel ch in
  print_term unfold ff t; pp_print_flush ff (); flush ch

let print_kind unfold ch t =
  let ff = formatter_of_out_channel ch in
  print_kind unfold false ff t; pp_print_flush ff (); flush ch

let print_kind_def unfold ch kd =
  let ff = formatter_of_out_channel ch in
  pkind_def unfold ff kd; pp_print_flush ff (); flush ch

let print_ordinal ch o =
  let ff = formatter_of_out_channel ch in
  print_ordinal false ff o; pp_print_flush ff (); flush ch

let print_reset_ordinals ch =
  let ff = formatter_of_out_channel ch in
  print_reset_ordinals ff; pp_print_flush ff (); flush ch

let reset_ordinals () =
  ordinal_count := 0;
  ordinal_tbl := []
