open Bindlib
open Format
open Ast
open Print

(****************************************************************************
 *                           Printing of a type                             *
 ****************************************************************************)

let break_hint = ref 0

let rec print_ordinal unfold ff o =
  let o = orepr o in
  match o with
  | OConv   -> pp_print_string ff "\\infty"
  | OTInt i -> fprintf ff "?%i" i
  | o       ->
     let n = search_ordinal_tbl o in
     match o with
     | OLess(o,In(t,a)) as o0 when unfold ->
        fprintf ff "\\kappa_{{<}%a}" (print_ordinal false) o;
        fprintf ff "(%a \\in %a)" (print_term false 0) t
          (print_kind false false) (subst a o0)
     | OLess(o,NotIn(t,a)) as o0 when unfold ->
        fprintf ff "\\kappa_{{<}%a}" (print_ordinal false) o;
        fprintf ff "(%a \\in %a)" (print_term false 0) t
          (print_kind false false) (subst a o0)
     | OLess(o,_) when unfold ->
       fprintf ff "\\alpha_{%d<%a}" n (print_ordinal false) o
     | OLess(_) -> fprintf ff "\\kappa_{%d}" n
     | OVari(x) -> fprintf ff "%s" (name_of x)
     | _ -> assert false

and print_index_ordinal ff o = match orepr o with
  | OConv -> ()
  | o -> fprintf ff "_{%a}" (print_ordinal false) o

and print_kind unfold wrap ff t =
  let pkind = print_kind false false in
  let pkindw = print_kind false true in
  let t = repr t in
  let key, _, ords = decompose false All t (KProd[]) in
  try
    if unfold then raise Not_found;
    let d = find_tdef key in
    let ords = List.filter (fun (_,o) -> orepr o <> OConv) ords in
    match ords with
    | [] -> fprintf ff "%s" d.tdef_tex_name
    | _  -> fprintf ff "%s_{%a}" d.tdef_tex_name
       (fun ff l -> List.iter (fun (i, o) -> fprintf ff "%s%a" (if i <> 0 then "," else "")
         (print_ordinal false) o) l) ords
  with Not_found ->
  match t with
  | KVari(x) ->
      pp_print_string ff (name_of x)
  | KFunc(a,b) ->
      if wrap then pp_print_string ff "(";
      fprintf ff "%a \\rightarrow %a" pkindw a pkind b;
      if wrap then pp_print_string ff ")"
  | KProd(fs) ->
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
         fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}";
         fprintf ff "\\begin{array}{ll}%a" (print_list pfield ";\\\\\n") fs;
         fprintf ff "\\end{array}\\right\\}"
       end
  | KDSum(cs) ->
     let pvariant ff (c,a) =
       match repr a with
       | KProd [] -> fprintf ff "\\mathrm{%s}" c
       | _        -> fprintf ff "\\mathrm{%s} \\of %a" c pkind a
     in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
  | KKAll(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_kvari (binder_name f) in
      fprintf ff "\\forall %s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | KKExi(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_kvari (binder_name f) in
      fprintf ff "\\exists %s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | KOAll(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_ovari (binder_name f) in
      fprintf ff "\\forall %s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | KOExi(f)  ->
      if wrap then pp_print_string ff "(";
      let x = new_ovari (binder_name f) in
      fprintf ff "\\exists%s.%a" (name_of x) pkind (subst f (free_of x));
      if wrap then pp_print_string ff ")"
  | KFixM(o,b) ->
      if wrap then pp_print_string ff "(";
      let x = new_kvari (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "\\mu%a %s %a" print_index_ordinal o (name_of x) pkind a;
      if wrap then pp_print_string ff ")"
  | KFixN(o,b) ->
      if wrap then pp_print_string ff "(";
      let x = new_kvari (binder_name b) in
      let a = subst b (free_of x) in
      fprintf ff "\\nu%a %s %a" print_index_ordinal o (name_of x) pkind a;
      if wrap then pp_print_string ff ")"
  | KDefi(td,args) ->
     if unfold then
       print_kind unfold wrap ff (msubst td.tdef_value args)
     else
       if Array.length args = 0 then
         pp_print_string ff td.tdef_tex_name
       else
         fprintf ff "%s(%a)" td.tdef_tex_name (print_array pkind ", ") args
  | KDPrj(t,s) ->
     fprintf ff "%a.%s" (print_term false 2) t s
  | KWith(a,(s,b)) ->
     fprintf ff "%a \\text{ with } %s = %a" pkind a s pkind b
  | KUCst(u,f)
  | KECst(u,f) ->
     let is_exists = match t with KECst(_) -> true | _ -> false in
     let name, index = search_type_tbl u f is_exists in
     fprintf ff "%s_{%d}" name index
  | KUVar(u) ->
      fprintf ff "?%i" u.uvar_key
  | KTInt(_) -> assert false
  | MuRec(_,a) -> pkind ff a
  | NuRec(_,a) -> pkind ff a


and pkind_def unfold ff kd =
  pp_print_string ff kd.tdef_tex_name;
  let names = mbinder_names kd.tdef_value in
  let xs = new_mvar mk_free_kvari names in
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
  | TCoer(t,a) ->
      fprintf ff "%a{:}%a" (print_term 2) t pkind a
  | TVari(x) ->
      pp_print_string ff (name_of x)
  | TAbst(_) ->
     if lvl > 0 then pp_print_string ff "(";
     let rec fn ff t = match t.elt with
       | TAbst(ao,b) ->
          let x = binder_name b in
          let t = subst b (free_of (new_tvari' x)) in
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
  | TKAbs(_) ->
     if lvl > 0 then pp_print_string ff "(";
     let rec fn ff t = match t.elt with
       | TKAbs(b) ->
          let x = binder_name b in
          let t = subst b (free_of (new_kvari x)) in
          fprintf ff " %s%a" x fn t
       | _        ->
          fprintf ff ".%a" (print_term 0) t
     in
     fprintf ff "\\Lambda %a" fn t;
     if lvl > 0 then pp_print_string ff ")";
  | TOAbs(_) ->
     if lvl > 0 then pp_print_string ff "(";
     let rec fn ff t = match t.elt with
       | TOAbs(b) ->
          let x = binder_name b in
          let t = subst b (free_of (new_ovari x)) in
          fprintf ff " %s%a" x fn t
       | _        ->
          fprintf ff ".%a" (print_term 0) t
     in
     fprintf ff "\\Lambda %a" fn t;
     if lvl > 0 then pp_print_string ff ")";
  | TAppl(t,u) ->
     if lvl > 1 then pp_print_string ff "(";
    fprintf ff "%a\\,%a" (print_term 1) t (print_term 2) u;
    if lvl > 1 then pp_print_string ff ")";
  | TReco(fs) ->
     if is_tuple fs then begin
       pp_print_string ff "(";
       for i = 1 to List.length fs do
         if i = 2 then fprintf ff ", ";
         fprintf ff "%a" (print_term 0) (List.assoc (string_of_int i) fs)
       done;
       pp_print_string ff ")";
     end else begin
       let fn s t =
         match t.elt with
         | TCoer(t,k) -> t, fun ff () -> fprintf ff "%s %a" s pkind k
         | _          -> t, fun ff () -> ()
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
         fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}";
         fprintf ff "\\begin{array}{ll}%a" (print_list pfield ";\\\\\n") fs;
         fprintf ff "\\end{array}\\right\\}"
       end
     end
  | TProj(t,l) ->
      fprintf ff "%a.\\mathrm{%s}" (print_term 0) t l
  | TCons(c,t) ->
     (match t.elt with
     | TReco([]) -> fprintf ff "\\mathrm{%s}" c
     | _         -> fprintf ff "\\mathrm{%s} %a" c (print_term 0) t)
  | TCase(t,l) ->
     let pvariant ff (c,b) =
       match b.elt with
       | TAbst(_,f) ->
          let x = binder_name f in
          let t = subst f (free_of (new_tvari' x)) in
          fprintf ff "\\mathrm{%s} %s \\rightarrow %a" c x (print_term 0) t
       | _          ->
          fprintf ff "\\mathrm{%s} \\rightarrow %a" c (print_term 0) b
      in
      fprintf ff "\\case{%a}{%a}" (print_term 0) t (print_list pvariant "| ") l
  | TDefi(v) ->
     if unfold then
       nprint_term lvl ff v.orig_value
     else
      pp_print_string ff v.tex_name
  | TPrnt(s) ->
      fprintf ff "print(%S)" s
  | TFixY(ko,f) ->
     if lvl > 0 then pp_print_string ff "(";
      let x = binder_name f in
      let t = subst f (free_of (new_tvari' x)) in
      fprintf ff "Y %s . %a" x (print_term 0) t;
     if lvl > 0 then pp_print_string ff ")";
  | TCnst(f,a,b) ->
     let name, index = search_term_tbl f a b in
     fprintf ff "%s_{%d}" name index
  | TTInt(i) ->
      fprintf ff "TAG(%i)" i

(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let term_to_string unfold t =
  print_term unfold 0 str_formatter t;
  flush_str_formatter ()

let kind_to_string unfold k =
  print_kind unfold false str_formatter k;
  flush_str_formatter ()

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
    let x = new_tvari dummy_position (binder_name f) in
    let t = subst f (free_of x) in
    Printf.fprintf ch "%s_{%d} &= \\epsilon_{%s \\in %a}( %a \\notin %a)\\\\\n" name index
      (name_of x) (print_kind false) a (print_term false) t (print_kind false) b) !epsilon_term_tbl;
  List.iter (fun (f,(name,index,u,is_exists)) ->
    let x = new_kvari (binder_name f) in
    let k = subst f (free_of x) in
    let symbol = if is_exists then "\\in" else "\\notin" in
      Printf.fprintf ch "%s_{%d} &= \\epsilon_{%s}(%a %s %a)\\\\\n" name index
      (name_of x) (print_term false) u symbol (print_kind false) k) !epsilon_type_tbl;
  List.iter (fun (o,n) ->
    Printf.fprintf ch "%a &= %a\\\\\n" (print_ordinal false) o (print_ordinal true) o) !ordinal_tbl

(****************************************************************************
 *                              Proof printing                              *
 ****************************************************************************)

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * type_def
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * Sct.calls_graph
  | TProof  of typ_prf
  | Sct     of Sct.calls_graph
  | Witnesses

let rec to_string = function
  | Text(t) -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _       -> assert false

let print_calls ch arities calls =
  let print_cmp ch c =
    match c with
    | Sct.Unknown -> Printf.fprintf ch "?"
    | Sct.Less    -> Printf.fprintf ch "<"
    | Sct.Leq     -> Printf.fprintf ch "="
  in
  let print_args ch i =
    let (_, a) = try List.assoc i arities with Not_found -> assert false in
    for i = 0 to a - 1 do
      Printf.fprintf ch "%sx_%d" (if i = 0 then "" else ",") i
    done
  in
  Printf.fprintf ch "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  List.iter (fun (i,_) ->
    Printf.fprintf ch "    N%d [ label = \"I_%d(%a)\" ];\n" i i print_args i) (List.filter (fun (i,_) ->
       List.exists (fun (j,k,_) -> i = j || i =k) calls) arities);
  let print_call arities (i,j,m) =
    Printf.fprintf ch "    N%d -> N%d [label = \"(" j i;
    Array.iteri (fun i l ->
      if i > 0 then Printf.fprintf ch ",";
      let some = ref false in
      Array.iteri (fun j c ->
	if c <> Sct.Unknown then (
	  let sep = if !some then " " else "" in
	  Printf.fprintf ch "%s%aX%d" sep print_cmp c j;
	  some := true
	)) l;
      if not !some then Printf.fprintf ch "?") m;
    Printf.fprintf ch ")\"]\n%!"
  in
  List.iter (print_call arities) calls;
  Printf.fprintf ch "  }\n\\end{dot2tex}\n"

let rec typ2proof : typ_prf -> string Proof.proof = fun (t,k,r) ->
  let open Proof in
  let t2s = term_to_string false and k2s = kind_to_string false in
  let c = Printf.sprintf "$%s : %s$" (t2s t) (k2s k) in
  match r with
  | Typ_Coer(p1,p2)   -> binaryN "$\\subset$" c (sub2proof p1) (typ2proof p2)
  | Typ_KAbs(p)       -> unaryN "$\\Lambda$" c (typ2proof p)
  | Typ_OAbs(p)       -> unaryN "$\\Lambda_o$" c (typ2proof p)
  | Typ_Defi(p)       -> hyp ""
  | Typ_Prnt(p)       -> unaryN "$print$" c (sub2proof p)
  | Typ_Cnst(p)       -> unaryN "$=$" c (sub2proof p)
  | Typ_Func_i(p1,p2) -> binaryN "$\\to_i$" c (sub2proof p1) (typ2proof p2)
  | Typ_Func_e(p1,p2) -> binaryN "$\\to_i$" c (typ2proof p1) (typ2proof p2)
  | Typ_Prod_i(p,ps)  -> n_aryN "$\\times_i$" c
                           (sub2proof p :: List.map typ2proof ps)
  | Typ_Prod_e(p)     -> unaryN "$\\times_e$" c (typ2proof p)
  | Typ_DSum_i(p1,p2) -> binaryN "$+_i$" c (sub2proof p1) (typ2proof p2)
  | Typ_DSum_e(p,ps)  -> n_aryN "$+_e$" c
                           (typ2proof p :: List.map typ2proof ps)
  | Typ_YH(n,p)          ->
     let name = Printf.sprintf "$H_%d$" n in
     unaryN name c (sub2proof p)
  | Typ_Y(n,p1,p)     ->
     let name = Printf.sprintf "$I_%d$" n in
     binaryN name c (sub2proof p1) (typ2proof p)

and     sub2proof : sub_prf -> string Proof.proof = fun (t,a,b,ir,r) ->
  let open Proof in
  let t2s = term_to_string false and k2s = kind_to_string false in
  let c = Printf.sprintf "$%s \\in %s \\subset %s$" (t2s t) (k2s a) (k2s b) in
  match r with
  | Sub_Delay(pr)     -> sub2proof !pr
  | Sub_Lower         -> hyp (Printf.sprintf "$%s \\leq %s$" (k2s a) (k2s b))
  | Sub_Func(p1,p2)   -> binaryN "$\\to$" c (sub2proof p1) (sub2proof p2)
  | Sub_Prod(ps)      -> n_aryN "$\\times$" c (List.map sub2proof ps)
  | Sub_DSum(ps)      -> n_aryN "$+$" c (List.map sub2proof ps)
  | Sub_DPrj_l(p1,p2) -> binaryN "$\\pi_l$" c (typ2proof p1) (sub2proof p2)
  | Sub_DPrj_r(p1,p2) -> binaryN "$\\pi_r$" c (typ2proof p1) (sub2proof p2)
  | Sub_With_l(p)     -> unaryN "$w_l$" c (sub2proof p)
  | Sub_With_r(p)     -> unaryN "$w_r$" c (sub2proof p)
  | Sub_KAll_r(p)     -> unaryN "$\\forall_r$" c (sub2proof p)
  | Sub_KAll_l(p)     -> unaryN "$\\forall_l$" c (sub2proof p)
  | Sub_KExi_l(p)     -> unaryN "$\\exists_l$" c (sub2proof p)
  | Sub_KExi_r(p)     -> unaryN "$\\exists_r$" c (sub2proof p)
  | Sub_OAll_r(p)     -> unaryN "$\\forall_{or}$" c (sub2proof p)
  | Sub_OAll_l(p)     -> unaryN "$\\forall_{ol}$" c (sub2proof p)
  | Sub_OExi_l(p)     -> unaryN "$\\exists_{ol}$" c (sub2proof p)
  | Sub_OExi_r(p)     -> unaryN "$\\exists_{or}$" c (sub2proof p)
  | Sub_FixM_r(p)     -> unaryN "$\\mu_r$" c (sub2proof p)
  | Sub_FixN_l(p)     -> unaryN "$\\nu_l$" c (sub2proof p)
  | Sub_FixM_l(p)     -> unaryN "$\\mu_l$" c (sub2proof p)
  | Sub_FixN_r(p)     -> unaryN "$\\nu_r$" c (sub2proof p)
  | Sub_Ind(n)        -> axiomN (Printf.sprintf "$H_%d$" n) c
  | Sub_Dummy         -> assert false (* Should not happen. *)

let print_typing_proof    ch p = Proof.output ch (typ2proof p)
let print_subtyping_proof ch p = Proof.output ch (sub2proof p)

let rec output ch = function
  | Kind(n,unfold,k) -> break_hint := n; print_kind unfold ch k; break_hint := 0
  | Term(n,unfold,t) -> break_hint := n; print_term unfold ch t; break_hint := 0
  | Text(t)        -> Printf.fprintf ch "%s" t
  | List(l)        -> Printf.fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  | SProof (p,(arities,calls)) ->
     print_subtyping_proof ch p;
     Printf.fprintf ch "\\begin{center}\n";
     if calls <> [] then print_calls ch arities calls;
     Printf.fprintf ch "\\end{center}\n%!";
  | TProof p       -> print_typing_proof ch p
  | Witnesses      -> print_epsilon_tbls ch; reset_epsilon_tbls ()
  | KindDef(n,t)     ->
     let name = t.tdef_tex_name in
     let f = t.tdef_value in
     let args = mbinder_names f in
     let params = Array.map (fun s -> free_of (new_kvari s)) args in
     let k = msubst f params in
     let print_array cg a =
       if Array.length a = 0 then () else
       Printf.fprintf ch "(%s%a)" a.(0) (fun ch a ->
         for i = 1 to Array.length a - 1 do
           Printf.fprintf ch ",%s" a.(i)
         done) a
     in
     break_hint := n;
     Printf.fprintf ch "%s%a &= %a" name print_array args (print_kind true) k;
     break_hint := 0
  | Sct (arities,calls) ->
      print_calls ch arities calls
