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

let is_tuple ls =
  let n = List.length ls in
  try
    for i = 1 to n do
      if not (List.mem_assoc (string_of_int i) ls) then raise Exit;
    done;
    true
  with
    Exit -> false

(* ordinals in this list are not printed, used
   to remove unused induction rule from printing *)
let ignored_ordinals = ref []

let rec onorm o =
  if List.memq o !ignored_ordinals then
    match o with OLess(o',_) | OInd(_,o') -> onorm o' | _ -> assert false
  else o

(* managment of a table to name ordinals and epsilon when printing *)
let ordinal_count = ref 0
let ordinal_tbl = ref []
let epsilon_term_tbl = ref[]
let epsilon_type_tbl = ref[]

let reset_epsilon_tbls () =
  ordinal_count := 0;
  ordinal_tbl := [];
  epsilon_term_tbl := [];
  epsilon_type_tbl := []

let search_type_tbl u f is_exists =
  try
    (* use the fact that f is liskely to be enough as a key.
       this is just for printing after all … *)
    let (name,index,_,_) = List.assq f !epsilon_type_tbl in
    (name, index)
  with not_found ->
    let base = binder_name f in
    let max = List.fold_left
      (fun acc (_,(base',i,u,is_exists)) -> if base = base' then max acc i else acc) (-1) !epsilon_type_tbl
    in
    let index = max + 1 in
    epsilon_type_tbl := (f,(base,index,u,is_exists)) :: !epsilon_type_tbl;
    (base, index)

let search_term_tbl f a b =
  try
    let (name,index,_,_) = List.assq f !epsilon_term_tbl in
    (name, index)
  with not_found ->
    let base = binder_name f in
    let max = List.fold_left
      (fun acc (_,(base',i,_,_)) -> if base = base' then max acc i else acc) (-1) !epsilon_term_tbl
    in
    let index = max + 1 in
    epsilon_term_tbl := (f,(base,index,a,b)) :: !epsilon_term_tbl;
    (base, index)

let search_ordinal_tbl o =
  try
    List.assq o !ordinal_tbl
  with
    Not_found ->
      let n = !ordinal_count in incr ordinal_count;
      ordinal_tbl := (o,n)::!ordinal_tbl;
      n

let print_term_in_subtyping = ref false


(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)
let simplified_ordinals = ref false

let rec print_ordinal unfold ff o =
  let o = onorm o in
  match o with
  | ODumm        -> pp_print_string ff "?"
  | OConv        -> pp_print_string ff "∞"
  | OTag i       -> fprintf ff "?%i" i
  | _ ->
    let n = search_ordinal_tbl o in
    match o with
    | OLess(o,In(t,a)) when unfold && not !simplified_ordinals ->
       fprintf ff "ϵ(<%a,%a∈%a)" (print_ordinal false) o
	 (print_term false) t (print_kind false false) a
    | OLess(o,NotIn(t,a)) when unfold && not !simplified_ordinals ->
       fprintf ff "ϵ(<%a,%a∉%a)" (print_ordinal false) o
	 (print_term false) t (print_kind false false) a
    | OInd(_,o) when unfold && !simplified_ordinals && onorm o <> OConv ->
       fprintf ff "α(%d≤%a)" n (print_ordinal false) o
    | OLess(o,_) when unfold && !simplified_ordinals ->
       fprintf ff "α(%d<%a)" n (print_ordinal false) o
    | OInd(_,o) -> fprintf ff "α%d" n
    | OLess(o,_) when !simplified_ordinals -> fprintf ff "α%d" n
    | OLess(o,_) -> fprintf ff "κ%d" n
    | _ -> assert false

and print_index_ordinal ff = function
  | OConv -> ()
  | o -> fprintf ff "[%a]" (print_ordinal !simplified_ordinals) o

and print_kind unfold wrap ff t =
  let pkind = print_kind unfold false in
  let pkindw = print_kind unfold true in
  let t = repr t in
  match t with
  | TVar(x) ->
      pp_print_string ff (name_of x)
  | Func(a,b) ->
      if wrap then pp_print_string ff "(";
      fprintf ff "%a → %a" pkindw a pkind b;
      if wrap then pp_print_string ff ")"
  | Prod(fs) ->
     if is_tuple fs && List.length fs > 0 then begin
       for i = 1 to List.length fs do
         if i = 2 then fprintf ff "×";
         fprintf ff "%a" pkindw (List.assoc (string_of_int i) fs)
       done
     end else begin
       let pfield ff (l,a) = fprintf ff "%s : %a" l pkind a in
       fprintf ff "{%a}" (print_list pfield "; ") fs
     end
  | DSum(cs) ->
      let pvariant ff (c,a) =
        if a = Prod [] then pp_print_string ff c
        else fprintf ff "%s of %a" c pkind a
      in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
  | FAll(f)  ->
      let x = new_tvar (binder_name f) in
      fprintf ff "∀%s %a" (name_of x) pkind (subst f (free_of x))
  | Exis(f)  ->
      let x = new_tvar (binder_name f) in
      fprintf ff "∃%s %a" (name_of x) pkind (subst f (free_of x))
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
  | DPrj(t,s) ->
     fprintf ff "%a.%s" (print_term false) t s
  | With(a,(s,b)) ->
     fprintf ff "%a with %s = %a" pkind a s pkind b
  | UCst(u,f)
  | ECst(u,f) ->
     let is_exists = match t with ECst(_) -> true | _ -> false in
     let name, index =search_type_tbl u f is_exists in
     fprintf ff "%s_%d" name index
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
 and position ff loc =
  let open Location in
  let open Lexing in
  let fname  = loc.loc_start.pos_fname in
  let lnum   = loc.loc_start.pos_lnum in
  let cstart = loc.loc_start.pos_cnum in
  let cend   = loc.loc_end.pos_bol - loc.loc_start.pos_bol + loc.loc_end.pos_cnum in
  fprintf ff "[File %S, line %d, characters %d-%d]" fname lnum cstart cend

and print_term unfold ff t =
  let print_term = print_term unfold in
  let pkind = print_kind false false in
  if not unfold && t.pos <> dummy_position then
    position ff t.pos
  else match t.elt with
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
  | KAbs(f) ->
     let x = binder_name f in
     let t = subst f (free_of (new_tvar (binder_name f))) in
     fprintf ff "Λ%s %a" x print_term t
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
       print_term ff v.orig_value
     else
       pp_print_string ff v.name
  | Prnt(s) ->
      fprintf ff "print(%S)" s
  | FixY(ko,f) ->
      let x = binder_name f in
      let t = subst f (free_of (new_lvar' x)) in
      begin
        match ko with
        | None   -> fprintf ff "fix %s → %a" x print_term t
        | Some a -> fprintf ff "fix(%s : %a) → %a" x pkind a print_term t
      end
  | Cnst(f,a,b) ->
     let name, index = search_term_tbl f a b in
     fprintf ff "%s_%d" name index

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

let _ = fprint_kind := print_kind

let print_kind_def unfold ch kd =
  let ff = formatter_of_out_channel ch in
  pkind_def unfold ff kd; pp_print_flush ff (); flush ch

let print_ordinal unfold ch o =
  let ff = formatter_of_out_channel ch in
  print_ordinal unfold ff o; pp_print_flush ff (); flush ch

let print_epsilon_tbls ch =
  List.iter (fun (f,(name,index,a,b)) ->
    let x = new_lvar dummy_position (binder_name f) in
    let t = subst f (free_of x) in
    Printf.fprintf ch "%s_%d = ϵ(%s ∈ %a, %a ∉ %a)\n" name index
      (name_of x) (print_kind false) a (print_term false) t (print_kind false) b) !epsilon_term_tbl;
  List.iter (fun (f,(name,index,u,is_exists)) ->
    let x = new_tvar (binder_name f) in
    let k = subst f (free_of x) in
    let symbol = if is_exists then "∈" else "∉" in
      Printf.fprintf ch "%s_%d = ϵ(%s, %a %s %a)\n" name index
      (name_of x) (print_term false) u symbol (print_kind false) k) !epsilon_type_tbl;
    List.iter (fun (o,n) ->
      Printf.fprintf ch "%a = %a\n" (print_ordinal false) o (print_ordinal true) o) !ordinal_tbl

exception Find_tdef of type_def

let find_tdef : kind -> type_def = fun t ->
  try
    Hashtbl.iter (fun _ d ->
      if d.tdef_arity = 0 && eq_kind (msubst d.tdef_value [||]) t then
	raise (Find_tdef d)) typ_env;
    raise Not_found
  with
    Find_tdef(t) -> t
