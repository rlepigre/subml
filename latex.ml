open Bindlib
open Format
open Ast
open Util
open Print

(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let break_hint = ref 0

let rec print_ordinal unfold ff o =
  let o = onorm o in
  match o with
  | OConv      -> pp_print_string ff "\\infty"
  | OTag i     -> fprintf ff "?%i" i
  | _ ->
     let n = search_ordinal_tbl o in
     match o with
     | OLess(o,In(t,a)) when unfold && not !simplified_ordinals ->
	fprintf ff "\\kappa_{{<}%a}(%a \\in %a)" (print_ordinal false) o (print_term false 0) t (print_kind false false) a
     | OLess(o,NotIn(t,a)) when unfold && not !simplified_ordinals ->
	fprintf ff "\\kappa_{{<}%a}(%a \\in %a)" (print_ordinal false) o (print_term false 0) t (print_kind false false) a
     | OInd(_,o) when unfold && !simplified_ordinals && onorm o <> OConv ->
	fprintf ff "\\alpha_{%d{\\leq}%a}" n (print_ordinal false) o
     | OLess(o,_) when unfold && !simplified_ordinals ->
       fprintf ff "\\alpha_{%d<%a}" n (print_ordinal false) o
     | OLess(_) when !simplified_ordinals -> fprintf ff "\\alpha_{%d}" n
     | OLess(_) -> fprintf ff "\\kappa_{%d}" n
     | OInd(_) -> fprintf ff "\\alpha_{%d}" n
     | _ -> assert false

and print_index_ordinal ff o = match onorm o with
  | OConv -> ()
  | o -> fprintf ff "_{%a}" (print_ordinal !simplified_ordinals) o

and print_kind unfold wrap ff t =
  let pkind = print_kind false false in
  let pkindw = print_kind false true in
  let t = repr t in
  let key, ords = decompose Both t in
  try
    if unfold then raise Not_found;
    let d = find_tdef key in
    let ords = List.filter (fun o -> onorm o <> OConv) ords in
    match ords with
    | [] -> fprintf ff "%s" d.tdef_tex_name
    | _  -> fprintf ff "%s_{%a}" d.tdef_tex_name
       (fun ff l -> List.iteri (fun i o -> fprintf ff "%s%a" (if i <> 0 then "," else "")
	 (print_ordinal !simplified_ordinals) o) l) ords
  with Not_found ->
  match t with
  | TVar(x) ->
      pp_print_string ff (name_of x)
  | Func(a,b) ->
      if wrap then pp_print_string ff "(";
      fprintf ff "%a \\rightarrow %a" pkindw a pkind b;
      if wrap then pp_print_string ff ")"
  | Prod(fs) ->
     if is_tuple fs then begin
       for i = 1 to List.length fs do
	 if i = 2 then fprintf ff "{\\times}";
	 fprintf ff "%a" pkindw (List.assoc (string_of_int i) fs)
       done
     end else
       if !break_hint = 0 then begin
	 let pfield ff (l,a) = fprintf ff "\\mathrm{%s} : %a" l pkind a in
	 fprintf ff "\\{%a\\}" (print_list pfield "; ") fs
       end else begin
	 decr break_hint;
	 let pfield ff (l,a) = fprintf ff "\\mathrm{%s} &: %a" l pkind a in
	 fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}\\begin{array}{ll}%a\\end{array}\\right\\}"
	   (print_list pfield ";\\\\\n")fs
       end
  | DSum(cs) ->
     let pvariant ff (c,a) =
       match repr a with
       | Prod [] -> fprintf ff "\\mathrm{%s}" c
       | _ -> fprintf ff "\\mathrm{%s} \\of %a" c pkind a
     in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
  | KAll(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_tvar (binder_name f) in
      fprintf ff "\\forall %s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | KExi(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_tvar (binder_name f) in
      fprintf ff "\\exists %s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | FixM(o,b) ->
      if wrap then pp_print_string ff "(";
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "\\mu%a %s %a" print_index_ordinal o (name_of x) pkind a;
      if wrap then pp_print_string ff ")"
  | FixN(o,b) ->
      if wrap then pp_print_string ff "(";
      let x = new_tvar (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "\\nu%a %s %a" print_index_ordinal o (name_of x) pkind a;
      if wrap then pp_print_string ff ")"
  | TDef(td,args) ->
     if unfold then
       print_kind unfold wrap ff (msubst td.tdef_value args)
     else
       if Array.length args = 0 then
         pp_print_string ff td.tdef_tex_name
       else
         fprintf ff "%s(%a)" td.tdef_tex_name (print_array pkind ", ") args
  | DPrj(t,s) ->
     fprintf ff "%a.%s" (print_term false 2) t s
  | With(a,(s,b)) ->
     fprintf ff "%a \\text{ with } %s = %a" pkind a s pkind b
  | UCst(u,f)
  | ECst(u,f) ->
     let is_exists = match t with ECst(_) -> true | _ -> false in
     let name, index = search_type_tbl u f is_exists in
     fprintf ff "%s_{%d}" name index
  | UVar(u) ->
      fprintf ff "?%i" u.uvar_key
  | TInt(_) -> assert false


and pkind_def unfold ff kd =
  pp_print_string ff kd.tdef_tex_name;
  let names = mbinder_names kd.tdef_value in
  let xs = new_mvar mk_free_tvar names in
  let k = msubst kd.tdef_value (Array.map free_of xs) in
  if Array.length names > 0 then
    fprintf ff "(%a)" (print_array pp_print_string ",") names;
  fprintf ff " = %a" (print_kind unfold false) k

(****************************************************************************
 *                           Printing of a term                             *
 ****************************************************************************)

and print_term unfold lvl ff t =
  let nprint_term = print_term false in
  let print_term = print_term unfold in
  let pkind = print_kind false false in
  match t.elt with
  | Coer(t,a) ->
      fprintf ff "%a{:}%a" (print_term 2) t pkind a
  | LVar(x) ->
      pp_print_string ff (name_of x)
  | LAbs(_) ->
     if lvl > 0 then pp_print_string ff "(";
     let rec fn ff t = match t.elt with
       | LAbs(ao,b) ->
	  let x = binder_name b in
	  let t = subst b (free_of (new_lvar' x)) in
	  begin
            match ao with
            | None   -> fprintf ff " %s%a" x fn t
            | Some a -> fprintf ff " %s{:}%a%a" x pkind a fn t
	  end
       | _ ->
	  fprintf ff ".%a" (print_term 0) t
     in
     fprintf ff "\\lambda%a" fn t;
     if lvl > 0 then pp_print_string ff ")";
  | KAbs(_) ->
     if lvl > 0 then pp_print_string ff "(";
     let rec fn ff t = match t.elt with
       | KAbs(b) ->
	  let x = binder_name b in
	  let t = subst b (free_of (new_tvar x)) in
          fprintf ff " %s%a" x fn t
       | _ ->
	  fprintf ff ".%a" (print_term 0) t
     in
     fprintf ff "\\Lambda %a" fn t;
     if lvl > 0 then pp_print_string ff ")";
  | Appl(t,u) ->
     if lvl > 1 then pp_print_string ff "(";
    fprintf ff "%a\\,%a" (print_term 1) t (print_term 2) u;
    if lvl > 1 then pp_print_string ff ")";
  | Reco(fs) ->
     if is_tuple fs then begin
       pp_print_string ff "(";
       for i = 1 to List.length fs do
	 if i = 2 then fprintf ff ", ";
	 fprintf ff "%a" (print_term 0) (List.assoc (string_of_int i) fs)
       done;
       pp_print_string ff ")";
     end else begin
       let fn s t = match t.elt with
	   Coer(t,k) -> t, fun ff () -> fprintf ff "%s %a" s pkind k
	 | _ -> t,  fun ff () -> ()
       in
       if !break_hint = 0 then begin
	 let pfield ff (l,t) =
	   let t, pt = fn ":" t in
	   fprintf ff "\\mathrm{%s} %a = %a" l pt () (print_term 0) t in
	 fprintf ff "\\{%a\\}" (print_list pfield "; ") fs
       end else begin
	 decr break_hint;
	 let pfield ff (l,t) =
	   let t, pt = fn ":" t in
	   fprintf ff "\\mathrm{%s} %a &= %a" l pt () (print_term 0) t
	 in
	 fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}\\begin{array}{ll}%a\\end{array}\\right\\}" (print_list pfield ";\\\\\n") fs
       end
     end
  | Proj(t,l) ->
      fprintf ff "%a.\\mathrm{%s}" (print_term 0) t l
  | Cons(c,t) ->
     (match t.elt with
     | Reco([]) -> fprintf ff "\\mathrm{%s}" c
     | _ -> fprintf ff "\\mathrm{%s} %a" c (print_term 0) t)
  | Case(t,l) ->
     let pvariant ff (c,b) =
       match b.elt with
       | LAbs(_,f) ->
          let x = binder_name f in
          let t = subst f (free_of (new_lvar' x)) in
          fprintf ff "| \\mathrm{%s} %s \\rightarrow %a" c x (print_term 0) t
       | _ ->
          fprintf ff "| \\mathrm{%s} \\rightarrow %a" c (print_term 0) b
      in
      fprintf ff "\\case{%a}{%a}" (print_term 0) t (print_list pvariant "; ") l
  | VDef(v) ->
     if unfold then
       nprint_term lvl ff v.orig_value
     else
      pp_print_string ff v.tex_name
  | Prnt(s) ->
      fprintf ff "print(%S)" s
  | FixY(ko,f) ->
     if lvl > 0 then pp_print_string ff "(";
      let x = binder_name f in
      let t = subst f (free_of (new_lvar' x)) in
      begin
        match ko with
        | None   -> fprintf ff "Y %s . %a" x (print_term 0) t
        | Some a -> fprintf ff "Y(%s : %a) . %a" x pkind a (print_term 0) t
      end;
     if lvl > 0 then pp_print_string ff ")";
  | Cnst(f,a,b) ->
     let name, index = search_term_tbl f a b in
     fprintf ff "%s_{%d}" name index
  | TagI(i) ->
      fprintf ff "TAG(%i)" i

(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let print_term unfold ch t =
  let ff = formatter_of_out_channel ch in
  print_term unfold 0 ff t; pp_print_flush ff (); flush ch

let print_kind unfold ch t =
  let ff = formatter_of_out_channel ch in
  print_kind unfold false ff t; pp_print_flush ff (); flush ch

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
    Printf.fprintf ch "%s_{%d} &= \\epsilon_{%s \\in %a}( %a \\notin %a)\\\\\n" name index
      (name_of x) (print_kind false) a (print_term false) t (print_kind false) b) !epsilon_term_tbl;
  List.iter (fun (f,(name,index,u,is_exists)) ->
    let x = new_tvar (binder_name f) in
    let k = subst f (free_of x) in
    let symbol = if is_exists then "\\in" else "\\notin" in
      Printf.fprintf ch "%s_{%d} &= \\epsilon_{%s}(%a %s %a)\\\\\n" name index
      (name_of x) (print_term false) u symbol (print_kind false) k) !epsilon_type_tbl;
  List.iter (fun (o,n) ->
    Printf.fprintf ch "%a &= %a\\\\\n" (print_ordinal false) o (print_ordinal true) o) !ordinal_tbl
