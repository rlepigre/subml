(****************************************************************************)
(**{3                               Ascii Printing                         }*)
(****************************************************************************)
open Bindlib
open Format
open Ast
open Position
open Compare
open LibTools

(** control some differences when printing for LaTeX *)
let latex_mode = ref false

(** [break_hint] allows line breaking for record, ...
    It gives the number of nested records whose lines are
    breaked *)
let break_hint = ref 0

(** ignore witness in subtyping proofs *)
let ignore_witness = ref true

(** list printing *)
let rec print_list pelem sep ff = function
  | []    -> ()
  | [e]   -> pelem ff e
  | e::es -> fprintf ff "%a%s%a" pelem e sep (print_list pelem sep) es

(** array printing *)
let rec print_array pelem sep ff ls =
  print_list pelem sep ff (Array.to_list ls)

(** test if a list of record fields is a tuple *)
let is_tuple ls =
  let n = List.length ls in
  try
    for i = 1 to n do
      if not (List.mem_assoc (string_of_int i) ls) then raise Exit;
    done;
    true
  with
    Exit -> false

(** Managment of a table to name all choice constants (for ordinals,
    terms and type) when printing.  terms and ordinals are named the
    first time they are printed.  The table of all names and
    definition can be printer later. *)
let ordi_count = ref 0
let ordi_tbl = ref []
let epsilon_term_tbl = ref[]
let epsilon_type_tbl = ref[]

let reset_epsilon_tbls () =
  ordi_count := 0;
  ordi_tbl := [];
  epsilon_term_tbl := [];
  epsilon_type_tbl := []

let search_type_tbl u f is_exists =
  try
    (* use the fact that f is liskely to be enough as a key.
       this is just for printing after all … *)
    let (name,index,_,_) = assoc_kkind f !epsilon_type_tbl in
    (name, index)
  with not_found ->
    let base = binder_name f in
    let fn acc (_,(base',i,u,is_exists)) =
      if base = base' then max acc i else acc
    in
    let max = List.fold_left fn (-1) !epsilon_type_tbl
    in
    let index = max + 1 in
    epsilon_type_tbl := (f,(base,index,u,is_exists)) :: !epsilon_type_tbl;
    (base, index)

let search_term_tbl (t:term) f =
  try
    assoc_term t !epsilon_term_tbl
  with not_found ->
    let base = binder_name f in
    let fn acc (_,(_,base',i)) =
      if base = base' then max acc i else acc
    in
    let max = List.fold_left fn (-1) !epsilon_term_tbl in
    let index = max + 1 in
    let name = "base_{" ^ string_of_int index ^ "}" in
    let t0 = dummy_pos (TVars name) in
    epsilon_term_tbl := (t,(t0,base,index)) :: !epsilon_term_tbl;
    (t0,base,index)

let search_ordi_tbl o =
  try
    fst (assoc_ordi o !ordi_tbl)
  with
    Not_found ->
      let n = !ordi_count in incr ordi_count;
      let v = OVari (new_ovari ("κ_{" ^ string_of_int n ^"}")) in
      ordi_tbl := (o,(v,false))::!ordi_tbl;
      v

(****************************************************************************)
(*{2                        Printing of ordinals                           }*)
(****************************************************************************)

let rec print_ordi unfold ff o =
  let o = orepr o in
  match o with
  | OConv   -> pp_print_string ff "∞"
  | OSucc(o) ->
     let rec fn i o =
       match orepr o with
         OSucc(o) -> fn (i+1) o
       | o -> fprintf ff "%a+%d" (print_ordi false) o i
     in fn 1 o
  | OUVar(u,os) ->
     let print_upper ff = function
       | (_,None) -> ()
       | (_,Some o) -> fprintf ff "<%a" (print_ordi false) (msubst o os)
     in
     let print_lower ff = function
       | (None,_) -> ()
       | (Some o,_) -> fprintf ff "%a≤" (print_ordi false) (msubst o os)
     in
     if os = [||] then
       fprintf ff "%a?%i%a" print_lower u.uvar_state u.uvar_key print_upper u.uvar_state
     else
       fprintf ff "%a?%i(%a)%a" print_lower u.uvar_state u.uvar_key
         (print_list print_index_ordi ", ") (Array.to_list os)
         print_upper u.uvar_state
  | OVari(x) -> fprintf ff "%s" (name_of x)
  | OLess(o,w) when unfold ->
     begin
       match w with
       | In(t,a) ->
          let ov = free_of (new_ovari "α") in
          fprintf ff "ε_{%a<%a}(%a∈%a)" (print_ordi false) ov (print_ordi false) o
            (print_term false) t (print_kind false false) (subst a ov)
       | NotIn(t,a) ->
          let ov = free_of (new_ovari "α") in
          fprintf ff "ε_{%a<%a}(%a∉%a)" (print_ordi false) ov (print_ordi false) o
            (print_term false) t (print_kind false false) (subst a ov)
       | Gen(i,r,f) ->
          let os = Array.init (mbinder_arity f)
            (fun i -> free_of (new_ovari ("α_{"^string_of_int i^"}"))) in
          let (k1,k2) = msubst f os in
          let os' = Array.mapi (fun i _ -> try os.(List.assoc i r) with Not_found -> OConv) os in
          fprintf ff "ε^%d_{%a<%a}(%a ⊂ %a)"
            i (print_array (print_ordi false) ",") os (print_array (print_ordi false) ",") os'
            (print_kind false false) k1 (print_kind false false) k2
     end
  | _ ->
    let o' = search_ordi_tbl o in print_ordi false ff o'

and print_index_ordi ff = function
  | OConv -> fprintf ff "∞"
  | o -> fprintf ff "%a" (print_ordi false) o

(****************************************************************************)
(*{2                         Printing of a type                            }*)
(****************************************************************************)

and new_prvar f = KPrnt(FreeVr(binder_name f))

and print_kind unfold wrap ff t =
  let pkind = print_kind false false in
  let pordi = print_ordi false in
  let pkindw = print_kind false true in
  let t = (if unfold then fun x -> x else !ftry_fold_def) (repr t) in
  match t with
  | KVari(x) ->
      pp_print_string ff (name_of x)
  | KFunc(a,b) ->
     if wrap then pp_print_string ff "(";
     fprintf ff "%a → %a" pkindw a pkind b;
     if wrap then pp_print_string ff ")"
  | KProd(fs) ->
     if is_tuple fs && List.length fs > 0 then begin
       if wrap then pp_print_string ff "(";
       for i = 1 to List.length fs do
         if i >= 2 then fprintf ff " × ";
         fprintf ff "%a" pkindw (List.assoc (string_of_int i) fs)
       done;
       if wrap then pp_print_string ff ")"
     end else
       if !break_hint = 0 then begin
         let pfield ff (l,a) =
           fprintf ff (if !latex_mode then "\\mathrm{%s} : %a" else "%s : %a")
             l pkind a
         in
         fprintf ff (if !latex_mode then "\\{%a\\}" else "{%a}")
           (print_list pfield "; ") fs
       end else begin
         decr break_hint;
         let pfield ff (l,a) = fprintf ff "\\mathrm{%s} &: %a" l pkind a in
         fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}";
         fprintf ff "\\begin{array}{ll}%a" (print_list pfield ";\\\\\n") fs;
         fprintf ff "\\end{array}\\right\\}";
         incr break_hint
       end
  | KDSum(cs) ->
      let pvariant ff (c,a) =
       match repr a with
       | KProd [] ->
          fprintf ff (if !latex_mode then "\\mathrm{%s}" else "%s") c
       | _        ->
          fprintf ff (if !latex_mode then "\\mathrm{%s} \\of %a" else "%s of %a")
            c pkind a
      in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
  | KKAll(f)  ->
      let x = new_prvar f in
      fprintf ff "∀%s.%a" (binder_name f) pkind (subst f x)
  | KKExi(f)  ->
      let x = new_prvar f in
      fprintf ff "∃%s.%a" (binder_name f) pkind (subst f x)
  | KOAll(f)  ->
      let x = new_ovari (binder_name f) in
      fprintf ff "∀%s.%a" (name_of x) pkind (subst f (free_of x))
  | KOExi(f)  ->
      let x = new_ovari (binder_name f) in
      fprintf ff "∃%s.%a" (name_of x) pkind (subst f (free_of x))
  | KFixM(o,b) ->
      let x = new_prvar b in
      let a = subst b x in
      if strict_eq_ordi o OConv then
        fprintf ff "μ%s.%a" (binder_name b) pkindw a
      else
        fprintf ff "μ_%a%s.%a" print_index_ordi o (binder_name b) pkindw a
  | KFixN(o,b) ->
      let x = new_prvar b in
      let a = subst b x in
      if strict_eq_ordi o OConv then
        fprintf ff "ν%s.%a" (binder_name b) pkindw a
      else
        fprintf ff "ν_%a%s.%a" print_index_ordi o (binder_name b) pkindw a
  | KDefi(td,os,ks) ->
     let name = if !latex_mode then td.tdef_tex_name else td.tdef_name in
     if unfold then
       print_kind unfold wrap ff (msubst (msubst td.tdef_value os) ks)
     else if Array.length ks = 0 && Array.length os = 0 then
       pp_print_string ff name
     else if Array.length os = 0 then
       fprintf ff "%s(%a)" name (print_array pkind ", ") ks
     else if Array.length ks = 0 then
       fprintf ff "%s_{%a}" name (print_array pordi ", ") os
     else
       fprintf ff "%s_{%a}(%a)" name (print_array pordi ", ") os
          (print_array pkind ", ") ks
  | KUCst(u,f,_)
  | KECst(u,f,_) ->
     let is_exists = match t with KECst(_) -> true | _ -> false in
     let name, index =search_type_tbl u f is_exists in
     fprintf ff "%s_%d" name index
  | KUVar(u,os) ->
     if os = [||] then
       fprintf ff "?%i" u.uvar_key
     else
       fprintf ff "?%i(%a)" u.uvar_key
         (print_list print_index_ordi ", ") (Array.to_list os)
  | KMRec(p,a) -> fprintf ff "(%a ∧ {%a})" pkind a
     (print_list (fun ff o -> pordi ff o) ", ") (Subset.unsafe_get p)
  | KNRec(p,a) -> fprintf ff "(%a ∨ {%a})" pkind a
     (print_list (fun ff o -> pordi ff o) ", ") (Subset.unsafe_get p)
  | KPrnt x -> match x with
  | FreeVr s -> pp_print_string ff s
  | DotPrj(x, s) -> fprintf ff "%s.%s" x s

(*
and print_state ff s os = match !s with
  | Free -> ()
  | Prod(fs) ->
     if is_tuple fs && List.length fs > 0 then begin
       pp_print_string ff "(";
       for i = 1 to List.length fs do
         if i >= 2 then fprintf ff " × ";
         fprintf ff "%a" (print_kind false true) (List.assoc (string_of_int i) fs)
       done;
       pp_print_string ff ")"
     end else begin
       let pfield ff (l,a) = fprintf ff "%s : %a" l (print_kind false true) a in
       fprintf ff "{%a}" (print_list pfield "; ") fs
     end
  | Sum(cs) ->
      let pvariant ff (c,a) =
        if a = KProd [] then pp_print_string ff c
        else fprintf ff "%s of %a" c (print_kind false true) a
      in
      fprintf ff "[%a]" (print_list pvariant " | ") cs
*)
and print_occur ff = function
  | All    -> pp_print_string ff "?"
  | Pos    -> pp_print_string ff "+"
  | Neg    -> pp_print_string ff "-"
  | Non    -> pp_print_string ff "="
  | Reg(_) -> pp_print_string ff "R"

and pkind_def unfold ff kd =
  let name = if !latex_mode then kd.tdef_tex_name else kd.tdef_name in
  fprintf ff "type %s" name;
  let pkind = print_kind unfold false in
  let onames = mbinder_names kd.tdef_value in
  let os = new_mvar mk_free_ovari onames in
  let k = msubst kd.tdef_value (Array.map free_of os) in
  let knames = mbinder_names k in
  let ks = new_mvar mk_free_kvari knames in
  let k = msubst k (Array.map free_of ks) in
  assert(Array.length knames = Array.length kd.tdef_kvariance);
  assert(Array.length onames = Array.length kd.tdef_ovariance);
  let onames = Array.mapi (fun i n -> (n, kd.tdef_ovariance.(i))) onames in
  let knames = Array.mapi (fun i n -> (n, kd.tdef_kvariance.(i))) knames in
  let print_elt ff (n,v) = fprintf ff "%s%a" n print_occur v in
  let parray = print_array print_elt "," in
  if Array.length knames = 0 && Array.length onames = 0 then
    fprintf ff " = %a" pkind k
  else if Array.length onames = 0 then
    fprintf ff "(%a) = %a" parray knames pkind k
  else if Array.length knames = 0 then
    fprintf ff "(%a) = %a" parray onames pkind k
  else
    fprintf ff "(%a,%a) = %a" parray onames parray knames pkind k

(****************************************************************************)
(*{2                         Printing of a term                            }*)
(****************************************************************************)
 and position ff pos =
  let open Position in
  fprintf ff "File %S, line %d, characters %d-%d"
    pos.filename pos.line_start pos.col_start pos.col_end

and print_term ?(in_proj=false) unfold ff t =
  let print_term = print_term false in
  let pkind = print_kind false false in
  (* TODO: temporary removed printing by position, should be optional *)
  (*let not_def t = match t.elt with TDefi _ -> false | _ -> true in
    if not !latex_mode && not in_proj && not unfold &&
    t.pos <> dummy_position && not_def t then
      fprintf ff "[%a]" position t.pos
    else *)
  match t.elt with
  | TCoer(t,a) ->
     fprintf ff "(%a : %a)" print_term t pkind a
  | TMLet(b,x,bt)->
     let (oa, ka) = mmbinder_arities bt OConv in
     let t = mmsubst bt (Array.make oa OConv) (Array.make ka (KProd [])) in
     fprintf ff "%a" print_term t (* FIXME *)
  | TVari(x) ->
      pp_print_string ff (name_of x)
  | TVars(s) ->
      pp_print_string ff s
  | TAbst(ao,b) ->
     let rec fn ff t = match t.elt with
       | TAbst(ao,b) ->
          let x = binder_name b in
          let t = subst b (TVars x) in
          begin
            match ao with
            | None   -> fprintf ff " %s%a" x fn t
            | Some a -> fprintf ff " %s{:}%a%a" x pkind a fn t
          end
       | _ ->
          fprintf ff ".%a" print_term t
     in
     fprintf ff "λ%a" fn t;
  | TAppl _ ->
     let rec fn ff t = match t.elt with
       | TAppl(t,u) ->
          fprintf ff "%a %a" fn t print_term u
       | _ ->
          fprintf ff "(%a)" print_term t
     in fn ff t
  | TReco(fs) ->
     if is_tuple fs then begin
       pp_print_string ff "(";
       for i = 1 to List.length fs do
         if i = 2 then fprintf ff ", ";
         fprintf ff "%a" print_term (List.assoc (string_of_int i) fs)
       done;
       pp_print_string ff ")";
     end else begin
       let fn s t =
         match t.elt with
         | TCoer(t,k) -> t, fun ff -> fprintf ff "%s %a" s pkind k
         | _          -> t, fun ff -> ()
       in
       if !break_hint = 0 then begin
         let pfield ff (l,t) =
           let t, pt = fn ":" t in
           fprintf ff (if !latex_mode then "\\mathrm{%s} %t = %a" else "%s %t = %a")
             l pt print_term t
         in
         fprintf ff (if !latex_mode then "\\{%a\\}" else "{%a}")
           (print_list pfield "; ") fs
       end else begin
         decr break_hint;
         let pfield ff (l,t) =
           let t, pt = fn ":" t in
           fprintf ff "\\mathrm{%s} %t &= %a" l pt print_term t
         in
         fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}";
         fprintf ff "\\begin{array}{ll}%a" (print_list pfield ";\\\\\n") fs;
         fprintf ff "\\end{array}\\right\\}";
         incr break_hint
       end
     end
  | TProj(t,l) ->
      fprintf ff "%a.%s" print_term t l
  | TCons(c,t) ->
     (match t.elt with
     | TReco([]) -> fprintf ff "%s" c
     | _         -> fprintf ff "%s %a" c print_term t)
  | TCase(t,l,d) ->
     let bar = ref "" in
     let pvariant ff (c,b) =
       match b.elt with
       | TAbst(_,f) ->
          let x = binder_name f in
          begin
            if x = "_" then
              fprintf ff "%s%s → %a" !bar c print_term t
            else
              let t = subst f (free_of (new_tvari x)) in
              fprintf ff "%s%s[%s] → %a" !bar c x print_term t;
          end;
          bar := "| "
       | _          ->
           assert false
     in
     let pdefault ff = function
       | None -> ()
       | Some({elt = TAbst(_,f)}) ->
           let x = binder_name f in
           let t = subst f (free_of (new_tvari x)) in
           fprintf ff "%s%s → %a" !bar x print_term t;
           bar := "| "
       | Some b           -> assert false
     in
     fprintf ff (if !latex_mode then "\\mathrm{case} %a \\mathrm{of} %a%a"
                                else "case %a of %a%a")
       print_term t (print_list pvariant " ") l pdefault d
  | TDefi(v) ->
     if unfold then
       print_term ff v.orig_value
     else
       let name = if !latex_mode then v.tex_name else v.name in
       pp_print_string ff name
  | TPrnt(s) ->
      fprintf ff "print(%S)" s
  | TFixY(_,_,f) ->
      let x = binder_name f in
      (*let t = subst f (TVars x) in*)
      (*fprintf ff "Y%s.%a" x print_term t*)
      fprintf ff "%s" x
  | TCnst(f,a,b,_) ->
     let t, name, index = search_term_tbl t f in
     if name = "" then
       print_term ff t
     else
       fprintf ff "%s_%d" name index

(****************************************************************************)
(*{2                           Proof to text                               }*)
(****************************************************************************)

let term_to_string unfold t =
  print_term unfold str_formatter t;
  flush_str_formatter ()

let kind_to_string unfold k =
  print_kind unfold false str_formatter k;
  flush_str_formatter ()


let rec sub_used_ind (t, k1, k2, r) =
  match r with
  | Sub_Delay { contents = p }
  | Sub_KAll_r p
  | Sub_KAll_l p
  | Sub_KExi_l p
  | Sub_KExi_r p
  | Sub_OAll_r p
  | Sub_OAll_l p
  | Sub_OExi_l p
  | Sub_OExi_r p
  | Sub_FixM_r p
  | Sub_FixN_l p
  | Sub_FixM_l p
  | Sub_FixN_r p
  | Sub_And_l  p
  | Sub_And_r  p
  | Sub_Or_l   p
  | Sub_Or_r   p
  | Sub_Gen(_,_,p)      -> sub_used_ind p
  | Sub_Func   (p1, p2) -> sub_used_ind p1 @ sub_used_ind p2
  | Sub_Prod   ps
  | Sub_DSum   ps       -> List.fold_left (fun acc (l,p) -> acc @ sub_used_ind p) [] ps
  | Sub_Ind n           -> [n]
  | Sub_Lower
  | Sub_Error _         -> []

and typ_used_ind (t, k, r) =
  match r with
  | Typ_Coer   (p2, p1)
  | Typ_Func_i (p2, p1)
  | Typ_DSum_i (p2, p1) -> typ_used_ind p1 @ sub_used_ind p2

  | Typ_Nope   p
  | Typ_TFix { contents = (_,p) }
  | Typ_Prod_e p        -> typ_used_ind p

  | Typ_Defi   p
  | Typ_Prnt   p
  | Typ_Cnst   p        -> sub_used_ind p

  | Typ_YH (n, p)       -> n :: sub_used_ind p

  | Typ_Func_e (p1, p2) -> typ_used_ind p1 @ typ_used_ind p2

  | Typ_Prod_i (p, ps)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (sub_used_ind p) ps
  | Typ_DSum_e (p, ps, None)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (typ_used_ind p) ps
  | Typ_DSum_e (p, ps, Some po)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (typ_used_ind p @ typ_used_ind po) ps

  | Typ_Hole
  | Typ_Error _       -> []

let is_refl : sub_prf -> bool = fun (t,a,b,r) -> strict_eq_kind a b

let rec typ2proof : Sct.index list -> typ_prf -> string Proof.proof = fun used_ind (t,k,r) ->
  let open Proof in
  let sub2proof = sub2proof used_ind in
  let typ2proof = typ2proof used_ind in
  let t2s = term_to_string true and k2s = kind_to_string false in
  let c = sprintf "%s : %s" (t2s t) (k2s k) in
  let binaryT name c p1 p2 =
    if is_refl p1 then unaryN name c p2
    else binaryN name c (sub2proof p1) p2
  in
  match r with
  | Typ_Coer(p1,p2)   -> binaryT "⊆" c p1 (typ2proof p2)
  | Typ_Nope(p)       -> typ2proof p
  | Typ_Defi(p)       -> unaryN "" c (sub2proof p)
  | Typ_Prnt(p)       -> unaryN "print" c (sub2proof p)
  | Typ_Cnst(p)       -> unaryN "Ax" c (sub2proof p)
  | Typ_Func_i(p1,p2) -> binaryT "→i" c p1 (typ2proof p2)
  | Typ_Func_e(p1,p2) -> binaryN "→e" c (typ2proof p1) (typ2proof p2)
  | Typ_Prod_i(p,ps)  -> n_aryN "×i" c (sub2proof p :: List.map typ2proof ps)
  | Typ_Prod_e(p)     -> unaryN "×e" c (typ2proof p)
  | Typ_DSum_i(p1,p2) -> binaryT "+i" c p1 (typ2proof p2)
  | Typ_DSum_e(p,ps,_)-> n_aryN "+e" c (typ2proof p :: List.map typ2proof ps) (* FIXME *)
  | Typ_YH(n,p)       ->
     let name = sprintf "[%s]" (Sct.strInd n) in
     unaryN name c (sub2proof p)
  | Typ_TFix{contents=(n,p)}     ->
     (* TODO: proof may be duplicated, print with sharing*)
     let name = sprintf "I_%s" (Sct.strInd n) in
     unaryN name c (typ2proof p)
  | Typ_Hole          -> axiomN "AXIOM" c
  | Typ_Error msg     -> axiomN (sprintf "ERROR(%s)" msg) c

and     sub2proof : Sct.index list -> sub_prf -> string Proof.proof =
  fun used_ind (t,a,b,r) ->
  let open Proof in
  let sub2proof = sub2proof used_ind in
  let t2s = term_to_string true and k2s = kind_to_string false in
  let mkJudgement t a b =
    if !ignore_witness then
      sprintf "%s ⊆ %s" (k2s a) (k2s b)
    else
      sprintf "%s ∈ %s ⊆ %s" (t2s t) (k2s a) (k2s b)
  in
  let mkSchema schema =
    let os = Array.init (mbinder_arity schema.sch_judge)
      (fun i -> new_ovari ("α_"^string_of_int i)) in
    let osnames = String.concat "," (Array.to_list (Array.map name_of os)) in
    let os = Array.map free_of os in
    let (a,b) = msubst schema.sch_judge os in
    sprintf "∀%s  %s ⊆ %s" osnames (k2s a) (k2s b)
  in
  let c = mkJudgement t a b in
  match r with
  | _ when strict_eq_kind a b
                      -> axiomN "$=$" c (* usefull because of unification *)
  | Sub_Delay(pr)     -> sub2proof !pr
  | Sub_Lower         -> axiomN "=" c
  | Sub_Func(p1,p2)   -> binaryN "→" c (sub2proof p1) (sub2proof p2)
  | Sub_Prod(ps)      -> n_aryN "×" c (List.map (fun (l,p) -> sub2proof p) ps)
  | Sub_DSum(ps)      -> n_aryN "+" c (List.map (fun (l,p) -> sub2proof p) ps)
  | Sub_KAll_r(p)     -> unaryN "∀_r" c (sub2proof p)
  | Sub_KAll_l(p)     -> unaryN "∀_l" c (sub2proof p)
  | Sub_KExi_l(p)     -> unaryN "∃_l" c (sub2proof p)
  | Sub_KExi_r(p)     -> unaryN "∃_r" c (sub2proof p)
  | Sub_OAll_r(p)     -> unaryN "∀^o_r" c (sub2proof p)
  | Sub_OAll_l(p)     -> unaryN "∀^o_l" c (sub2proof p)
  | Sub_OExi_l(p)     -> unaryN "∃o_l" c (sub2proof p)
  | Sub_OExi_r(p)     -> unaryN "∃o_r" c (sub2proof p)
  | Sub_FixM_r(p)     -> unaryN "μ_r" c (sub2proof p)
  | Sub_FixN_l(p)     -> unaryN "ν_l" c (sub2proof p)
  | Sub_FixM_l(p)     -> unaryN "μ_l" c (sub2proof p)
  | Sub_FixN_r(p)     -> unaryN "ν_r" c (sub2proof p)
  | Sub_And_l(p)      -> unaryN "∧_l" c (sub2proof p)
  | Sub_And_r(p)      -> unaryN "∧_r" c (sub2proof p)
  | Sub_Or_l(p)       -> unaryN "∨_l" c (sub2proof p)
  | Sub_Or_r(p)       -> unaryN "∨_r" c (sub2proof p)
  | Sub_Ind(n)        -> axiomN (sprintf "[%s]" (Sct.strInd n)) c
  | Sub_Error(msg)    -> axiomN (sprintf "ERROR(%s)" msg) c
  | Sub_Gen(schema,tros,((t0,_,_,_) as p)) ->
     if List.mem schema.sch_index used_ind then (
       let c0 = mkSchema schema in
       unaryN "G^+_e" c
         (unaryN ("G^+_i["^ Sct.strInd schema.sch_index ^"]") c0 (sub2proof p)))
     else (
         ordi_tbl := List.map (fun (o1,o2) -> (o1,(o2,true))) tros @ !ordi_tbl;
         epsilon_term_tbl := (t,(t0,"",-1)) :: !epsilon_term_tbl;
         sub2proof p)

let sub2proof p = sub2proof (sub_used_ind p) p
let typ2proof p = typ2proof (typ_used_ind p) p
let print_typing_proof    ch p = Proof.output ch (typ2proof p)
let print_subtyping_proof ch p = Proof.output ch (sub2proof p)


(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let print_term unfold ff t =
  print_term unfold ff t; pp_print_flush ff ()

let print_kind unfold ff t =
  print_kind unfold false ff t; pp_print_flush ff ()

let _ = fprint_kind := print_kind; fprint_term := print_term

let print_kind_def unfold ff kd =
  pkind_def unfold ff kd; pp_print_flush ff ()

let print_ordi unfold ff o =
  print_ordi unfold ff o; pp_print_flush ff ()

let print_position ff o =
  position ff o; pp_print_flush ff ()

let print_epsilon_tbls ff =
  list_ref_iter (fun (t,(t0,name,index)) ->
    match t.elt with
    | TCnst(f,a,b,_) when name <> "" ->
       let x = free_of (new_tvari (binder_name f)) in
       let t = subst f x in
       fprintf ff "%s_%d &= ε_{%a ∈ %a}(%a ∉ %a)\\\\\n" name index
         (print_term false) (dummy_pos x)
         (print_kind false) a (print_term false) t (print_kind false) b
    | _ when name = "" ->
       ()
    | _ -> assert false)
    epsilon_term_tbl;
  list_ref_iter (fun (f,(name,index,u,is_exists)) ->
    let x = new_prvar f in
    let k = subst f x in
    let symbol = if is_exists then "∈" else "∉" in
      fprintf ff "%s_%d &= ε_%s(%a %s %a)\\\\\n" name index
      (binder_name f) (print_term false) u symbol (print_kind false) k) epsilon_type_tbl;
  list_ref_iter (fun (o,(n,defi)) ->
    if not defi then
      fprintf ff "%a &= %a\\\\\n" (print_ordi false) n (print_ordi true) o) ordi_tbl

exception Find_tdef of kdef

let find_tdef : kind -> kdef = fun t ->
  try
    let fn _ d =
      if d.tdef_oarity = 0 && d.tdef_karity = 0 then
        let k = msubst (msubst d.tdef_value [||]) [||] in
        if strict_eq_kind k t then raise (Find_tdef d)
    in
    Hashtbl.iter fn typ_env;
    raise Not_found
  with
    Find_tdef(t) -> t

let _ = fprint_ordi := print_ordi

let ordi_to_printer (_,o) ff = print_ordi false ff o
