(****************************************************************************)
(**{3                               Ascii Printing                         }*)
(****************************************************************************)
open Bindlib
open Format
open Ast
open Pos
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
    let t0 = Pos.none (TVars name) in
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

let skip_record_sugar name t =
  let nb =
    if String.length name > 2 && name.[0] = ':' then 2
    else
      let r = ref 0 in
      String.iter (function ';' | '(' | ',' -> incr r | _ -> ()) name;
      !r
  in
  let rec fn n t = match t.elt with
    | TAppl({ elt = TAbst(_,f) },_) when n > 0 ->
       let x = TVars (binder_name f) in
       fn (n-1) (subst f x)
    | t -> assert(n=0); t
  in
  Pos.none (fn nb t)

(** A test to avoid capture in match_kind below *)
let has_kvar : kind -> bool = fun k ->
  let rec fn k =
    match repr k with
    | KFunc(a,b) -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)  -> List.iter (fun (l,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)   -> fn (subst f (KProd []))
    | KFixM(o,f) -> gn o; fn (subst f (KProd []))
    | KFixN(o,f) -> gn o; fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)   -> fn (subst f OConv)
    | KUVar(u,_) -> ()
    | KDefi(d,o,a) -> Array.iter fn a
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | KVari _    -> raise Exit
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd []))
    | KPrnt _    -> ()
  and gn o = match orepr o with
    | OUVar _ -> ()
    | OConv -> ()
    | OSucc o -> gn o
    | OLess(o,_) -> gn o (* TODO: look at the witness *)
    | OVars _ -> ()
    | OVari _ -> raise Exit
  in
  try
    fn k; false
  with
    Exit -> true

(** Matching kind and ordinals, used for printing only,
    in order to factorise definittion. *)
let rec match_kind : kuvar list -> ouvar list -> kind -> kind -> bool
  = fun kuvars ouvars p k ->
  let res = match full_repr p, full_repr k with
    | KUVar(ua,[||]), k when List.memq ua kuvars ->
     set_kuvar ua (constant_mbind 0 k); not (has_kvar p) (* NOTE: to avoid capture *)
  | KFunc(p1,p2), KFunc(k1,k2) ->
     match_kind kuvars ouvars p1 k1 && match_kind kuvars ouvars p2 k2
  | KDSum(ps1), KDSum(ps2)
  | KProd(ps1), KProd(ps2) ->
     List.length ps1 = List.length ps2 &&
     let ps1 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps1 in
     let ps2 = List.sort (fun (s1,_) (s2,_) -> compare s1 s2) ps2 in
     List.for_all2 (fun (s1,p1) (s2,k1) ->
       s1 = s2 && match_kind kuvars ouvars p1 k1) ps1 ps2
  | KKAll(f), KKAll(g)
  | KKExi(f), KKExi(g) ->
     let v = new_kvari (binder_name f) in
     match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KOAll(f), KOAll(g)
  | KOExi(f), KOExi(g) ->
     let v = new_ovari (binder_name f) in
     match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KFixM(o1,f), KFixM(o2,g)
  | KFixN(o1,f), KFixN(o2,g) ->
     let v = new_kvari (binder_name f) in
     match_ordi ouvars o1 o2 &&
       match_kind kuvars ouvars (subst f (free_of v)) (subst g (free_of v))
  | KVari(v1), KVari(v2) -> compare_vars v1 v2 = 0
  | p, k -> strict_eq_kind p k
  in
  res

and match_ordi : ouvar list -> ordi -> ordi -> bool = fun ouvars p o ->
  let orepr o =
    let o = orepr o in
    try fst (assoc_ordi o !ordi_tbl)
    with Not_found -> o
  in
  let res = match orepr p, orepr o with
    | OUVar(uo,_), o when List.memq uo ouvars ->
       set_ouvar uo (constant_mbind 0 o); true
    | OSucc(p), OSucc(o) -> match_ordi ouvars p o
    | p, k -> strict_eq_ordi p k in
  res

let try_fold_def : kind -> kind = fun k ->
  let save_debug = !Io.debug in
  Io.debug := "";
  let match_def k def = (* TODO: share code with TMLet *)
    let kargs = Array.init def.tdef_karity (fun n -> new_kuvar ()) in
    let oargs = Array.init def.tdef_oarity (fun n -> new_ouvar ()) in
    let lkargs = List.map (function KUVar(u,_) -> u | _ -> assert false)
      (Array.to_list kargs) in
    let loargs = List.map (function OUVar(u,_) -> u | _ -> assert false)
      (Array.to_list oargs) in
    let k' = KDefi(def,oargs,kargs) in
    if match_kind lkargs loargs k' k then k' else raise Not_found;
  in
  let res =
    match repr k with
    | KDefi _ -> k
    | _ ->
       let defs = Hashtbl.fold (fun _ a l -> a::l) typ_env [] in
       let defs = List.sort
         (fun d1 d2 -> compare (d1.tdef_karity + d1.tdef_oarity)
                               (d2.tdef_karity + d2.tdef_oarity)) defs
       in
       let rec fn = function
         | [] -> k
         | def::l ->
            try
              match_def k def
            with
              Not_found -> fn l
       in
       fn defs
  in
  Io.debug := save_debug;
  res

(****************************************************************************)
(*{2                        Printing of ordinals                           }*)
(****************************************************************************)

let rec print_ordi unfold unfolded_Y ff o =
  let o = orepr o in
  let pordi = print_ordi false unfolded_Y in
  let pkind = print_kind false false unfolded_Y in
  match o with
  | OConv   -> pp_print_string ff "∞"
  | OSucc(o) ->
     let rec fn i o =
       match orepr o with
         OSucc(o) -> fn (i+1) o
       | o -> fprintf ff "%a+%d" pordi o i
     in fn 1 o
  | OUVar(u,os) ->
     let print_upper ff = function
       | (_,None) -> ()
       | (_,Some o) -> fprintf ff "<%a" pordi (msubst o os)
     in
     let print_lower ff = function
       | (None,_) -> ()
       | (Some o,_) -> fprintf ff "%a≤" pordi (msubst o os)
     in
     if os = [||] then
       fprintf ff "%a?%i%a" print_lower (uvar_state u)
               u.uvar_key print_upper (uvar_state u)
     else
       fprintf ff "%a?%i(%a)%a" print_lower (uvar_state u) u.uvar_key
         (print_list print_index_ordi ", ") (Array.to_list os)
         print_upper (uvar_state u)
  | OVari(x) -> fprintf ff "%s" (name_of x)
  | OVars(s) -> fprintf ff "%s" s
  | OLess(o,w) when unfold ->
     begin
       match w with
       | In(t,a) ->
          let ov = OVars "α" in
          fprintf ff "ε_{%a<%a}(%a∈%a)" pordi ov pordi o
            (print_term false false None) t pkind (subst a ov)
       | NotIn(t,a) ->
          let ov = OVars "α" in
          fprintf ff "ε_{%a<%a}(%a∉%a)" pordi ov pordi o
            (print_term false false None) t pkind (subst a ov)
       | Gen(i,s) ->
          let r = s.sch_relat in
          let f = s.sch_judge in
          let os = Array.init (mbinder_arity f)
            (fun i -> OVars ("α_{"^string_of_int (i+1)^"}")) in
          let (k1,k2) = msubst f os in
          let os' = Array.mapi (fun i _ -> try os.(List.assoc i r)
                                           with Not_found -> OConv) os in
          match k1 with
          | SchTerm t ->
             fprintf ff "ε^%d_{%a<%a}(%a \\notin %a)"
               (i+1) (print_array pordi ",") os (print_array pordi ",") os'
               (print_term false false None) (Pos.none (TFixY(None,0,t))) pkind k2
          | SchKind k1 ->
             fprintf ff "ε^%d_{%a<%a}(%a \\not\\subset %a)"
               (i+1) (print_array pordi ",") os (print_array pordi ",") os'
               pkind k1 pkind k2
     end
  | _ ->
    let o' = search_ordi_tbl o in pordi ff o'

and print_index_ordi ff = function
  | OConv -> fprintf ff "∞"
  | o -> fprintf ff "%a" (print_ordi false None) o

(****************************************************************************)
(*{2                         Printing of a type                            }*)
(****************************************************************************)

and new_prvar f = KPrnt(FreeVr(binder_name f))

and print_kind unfold wrap unfolded_Y ff t =
  let pkind = print_kind false false unfolded_Y in
  let pordi = print_ordi false unfolded_Y in
  let pkindw = print_kind false true unfolded_Y in
  let t = (if unfold then fun x -> x else try_fold_def) (repr t) in
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
      let x = OVars (binder_name f) in
      fprintf ff "∀%s.%a" (binder_name f) pkind (subst f x)
  | KOExi(f)  ->
      let x = OVars (binder_name f) in
      fprintf ff "∃%s.%a" (binder_name f) pkind (subst f x)
  | KFixM(o,b) ->
      let x = new_prvar b in
      let a = subst b x in
      if strict_eq_ordi o OConv then
        fprintf ff "μ%s.%a" (binder_name b) pkindw a
      else
        fprintf ff "μ_{%a}%s.%a" print_index_ordi o (binder_name b) pkindw a
  | KFixN(o,b) ->
      let x = new_prvar b in
      let a = subst b x in
      if strict_eq_ordi o OConv then
        fprintf ff "ν%s.%a" (binder_name b) pkindw a
      else
        fprintf ff "ν_{%a}%s.%a" print_index_ordi o (binder_name b) pkindw a
  | KDefi(td,os,ks) ->
     let name = if !latex_mode then td.tdef_tex_name else td.tdef_name in
     if unfold then
       print_kind true wrap unfolded_Y ff (msubst (msubst td.tdef_value os) ks)
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
     fprintf ff "%s_{%d}" name index
  | KUVar(u,os) ->
     if os = [||] then
       fprintf ff "?%i" u.uvar_key
     else
       fprintf ff "?%i(%a)" u.uvar_key
         (print_list print_index_ordi ", ") (Array.to_list os)
  | KMRec(p,a) ->
     if wrap then pp_print_string ff "(";
     fprintf ff "%a ∧ {%a}" pkindw a
       (print_list (fun ff o -> pordi ff o) ", ") (Subset.unsafe_get p);
     if wrap then pp_print_string ff ")";
  | KNRec(p,a) ->
     if wrap then pp_print_string ff "(";
     fprintf ff "%a ∨ {%a}" pkindw a
       (print_list (fun ff o -> pordi ff o) ", ") (Subset.unsafe_get p);
     if wrap then pp_print_string ff ")";
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
  | All      -> pp_print_string ff "?"
  | Pos true -> pp_print_string ff "++"
  | Neg true -> pp_print_string ff "--"
  | Pos _    -> pp_print_string ff "+"
  | Neg _    -> pp_print_string ff "-"
  | Non      -> pp_print_string ff "="
  | Reg(_)   -> pp_print_string ff "R"

and pkind_def unfold ff kd =
  let name = if !latex_mode then kd.tdef_tex_name else kd.tdef_name in
  fprintf ff "type %s" name;
  let pkind = print_kind unfold false None in
  let onames = mbinder_names kd.tdef_value in
  let os = new_mvar mk_free_o onames in
  let k = msubst kd.tdef_value (Array.map free_of os) in
  let knames = mbinder_names k in
  let ks = new_mvar mk_free_k knames in
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

and print_term ?(give_pos=false) unfold wrap unfolded_Y ff t =
  let wterm = print_term ~give_pos false true unfolded_Y in
  let pterm = print_term ~give_pos false false unfolded_Y in
  let pkind = print_kind false false unfolded_Y in
  if not !latex_mode && give_pos && not unfold && t.pos <> None then
    let pos = from_opt (map_opt short_pos_to_string t.pos) "..." in
    fprintf ff "[%s]" pos
  else match t.elt with
  | TCoer(t,a) ->
     if wrap then fprintf ff "(";
     fprintf ff "%a : %a" (print_term ~give_pos unfold wrap unfolded_Y) t pkind a;
     if wrap then fprintf ff ")"
  | TMLet(b,x,bt)->
     let (onames, knames) = mmbinder_names bt OConv in
     let ovars = Array.map (fun n -> free_of (new_ovari n)) onames in
     let kvars = Array.map (fun n -> free_of (new_kvari n)) knames in
     let t = mmsubst bt ovars kvars in
     let k = mmsubst b ovars kvars in
     let print_name ff = fprintf ff "%s" in
     let pnames = print_array print_name "," in
     let popt ff = function
       | None -> fprintf ff (if !latex_mode then "\\_" else "_")
       | Some t -> pterm ff t
     in
     fprintf ff (if !latex_mode then
         if !break_hint = 0 then
           "\\LET %a \\ST %a:%a \\IN %a"
         else
           "\\begin{array}[t]{l}\\LET %a \\ST %a:%a \\IN\\\\ %a\\end{array}"
       else
         "let %a such that %a:%a in %a")
       pnames (Array.append onames knames)
       popt x pkind k pterm t
  | TVari(x) ->
      pp_print_string ff (name_of x)
  | TVars(s) ->
      pp_print_string ff s
  | TAbst(ao,b) ->
     if wrap then fprintf ff "(";
     let rec fn first ff t = match t.elt with
       | TAbst(ao,b) ->
          let x = binder_name b in
          let t = subst b (TVars x) in
          let sep = if first then "" else
                      if !latex_mode then "\\, " else " " in
          let p = if !latex_mode && String.length x > 0 &&
                            x.[0] = '{' then "\\record" else ""
          in
          let t = skip_record_sugar x t in
          begin
            match ao with
            | None   -> fprintf ff "%s%s%s%a" sep p x (fn false) t
            | Some a -> fprintf ff "%s%s%s{:}%a%a" sep p x pkind a (fn false) t
          end
       | _ ->
          fprintf ff ".%a" pterm t
     in
     fprintf ff "λ%a" (fn true) t;
     if wrap then fprintf ff ")"

  | TAppl _ ->
    if wrap then fprintf ff "(";
    let rec fn acc t = match t.elt with
       | TAppl(t,u) ->
          fn (u::acc) t
       | _ ->
          t::acc
     in
     let terms = fn [] t in
     let sep = if !latex_mode then " \\; " else " " in
     print_list wterm sep ff terms;
     if wrap then fprintf ff ")"

  | TReco(fs) ->
     if is_tuple fs then begin
       pp_print_string ff "(";
       for i = 1 to List.length fs do
         if i = 2 then fprintf ff ", ";
         fprintf ff "%a" pterm (List.assoc (string_of_int i) fs)
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
             l pt pterm t
         in
         fprintf ff (if !latex_mode then "\\{%a\\}" else "{%a}")
           (print_list pfield "; ") fs
       end else begin
         decr break_hint;
         let pfield ff (l,t) =
           let t, pt = fn ":" t in
           fprintf ff "\\mathrm{%s} %t &= %a" l pt pterm t
         in
         fprintf ff "\\left\\{\\setlength{\\arraycolsep}{0.2em}";
         fprintf ff "\\begin{array}{ll}%a" (print_list pfield ";\\\\\n") fs;
         fprintf ff "\\end{array}\\right\\}";
         incr break_hint
       end
     end
  | TProj(t,l) ->
      fprintf ff "%a.%s" pterm t l
  | TCons(c,t) ->
     if wrap then fprintf ff "(";
     (match c, t.elt with
     | "Nil", TReco [] -> fprintf ff "[]"
     | "Cons", TReco l when List.sort compare (List.map fst l) = ["hd"; "tl"] ->
        fprintf ff "%a{::}%a" pterm (List.assoc "hd" l)  pterm (List.assoc "tl" l)
     | _, TReco([]) -> fprintf ff "%s" c
     | _         -> fprintf ff "%s %a" c wterm t);
       if wrap then fprintf ff ")";
  | TCase(t,l,d) ->
     if List.length l = 1 && d = None && snd (List.hd l) == unbox idt then begin
       fprintf ff "%a.%s" pterm t (fst (List.hd l))
     end else begin
       let bar = ref "" in
       let pvariant fin ff (c,b) =
         match b.elt with
         | TAbst(_,f) ->
            let x0 = binder_name f in
            begin
              let t = subst f (free_of (new_tvari x0)) in
              if x0 = "" then
                let c = if c = "Nil" then "[]" else c in
                fprintf ff "%s%s → %a" !bar c pterm t
              else
                let (c,x,prefix) =
                  if c = "Cons" && String.length x0 > 0 && x0.[0] = ':' then
                    ("",String.sub x0 1 (String.length x0 - 1), "")
                  else
                    let p = if !latex_mode && String.length x0 > 0 &&
                      x0.[0] = '{' then "\\record" else ""
                    in
                    (c, x0, p)
                in
                fprintf ff "%s%s %s%s → %a" !bar c prefix x pterm (skip_record_sugar x0 t);
            end;
            bar := if !latex_mode then (if fin = "" then "\\mid " else fin) else "| "
         | _          ->
            assert false
       in
       let pdefault ff = function
         | None -> ()
         | Some({elt = TAbst(_,f)}) ->
            let x = binder_name f in
            let t = subst f (free_of (new_tvari x)) in
            fprintf ff "%s%s → %a" !bar x pterm t;
         | Some b           -> assert false
       in
       if !break_hint > 0 then begin
         decr break_hint;
         fprintf ff "\\casearray{%a}{\\begin{array}{l}%a%a\\end{array}}"
           pterm t (print_list (pvariant "\\\\") " ") l pdefault d;
         incr break_hint
       end else
         fprintf ff (if !latex_mode then "\\case{%a}{%a%a}"
           else "case %a of %a%a")
           pterm t (print_list (pvariant "") " ") l pdefault d
     end
  | TDefi(v) ->
     if unfold then
       print_term
         ~give_pos true wrap unfolded_Y ff v.orig_value
     else
       let name = if !latex_mode then v.tex_name else v.name in
       pp_print_string ff name
  | TPrnt(s) ->
      fprintf ff "print(%S)" s
  | TFixY(_,_,f) ->
     let x = binder_name f in
     (match unfolded_Y with
     | Some l when not (List.memq f l) ->
        let unfolded_Y = Some (f :: l) in
        let t = subst f (TVars x) in
        fprintf ff "Y%s.%a" x (print_term ~give_pos false false unfolded_Y) t
     | _ ->
        fprintf ff (if !latex_mode then "\\mathrm{%s}" else "%s") x)
  | TCnst(f,a,b) ->
     let t, name, index = search_term_tbl t f in
     if name = "" then
       pterm ff t
     else
       fprintf ff "%s_{%d}" name index

(****************************************************************************)
(*{2                           Proof to text                               }*)
(****************************************************************************)

let term_to_string unfold t =
  print_term unfold false None str_formatter t;
  flush_str_formatter ()

let ordi_to_string unfold t =
  print_ordi unfold None str_formatter t;
  flush_str_formatter ()

let kind_to_string unfold k =
  print_kind unfold false None str_formatter k;
  flush_str_formatter ()


let rec sub_used_ind (_, _, _, _, r) =
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
  | Sub_Ind sch         -> [sch.sch_index]
  | Sub_Lower
  | Sub_Error _         -> []

and typ_used_ind (_, _, _, r) =
  let rec fn ptr = match !ptr with
    | Todo              -> []
    | Unroll(_,_,p)     -> typ_used_ind p
    | Induction(s,p)    -> s.sch_index :: sub_used_ind p
  in
  match r with
  | Typ_YGen ptr        -> fn ptr

  | Typ_Coer   (p2, p1)
  | Typ_Func_i (p2, p1)
  | Typ_DSum_i (p2, p1) -> typ_used_ind p1 @ sub_used_ind p2

  | Typ_Nope   p
  | Typ_Yufl   p
  | Typ_Prod_e p        -> typ_used_ind p

  | Typ_Defi   p
  | Typ_Prnt   p
  | Typ_Cnst   p        -> sub_used_ind p

  | Typ_Func_e (p1, p2) -> typ_used_ind p1 @ typ_used_ind p2

  | Typ_Prod_i (p, ps)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (sub_used_ind p) ps
  | Typ_DSum_e (p, ps, None)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (typ_used_ind p) ps
  | Typ_DSum_e (p, ps, Some po)
    -> List.fold_left (fun acc p -> acc @ typ_used_ind p) (typ_used_ind p @ typ_used_ind po) ps

  | Typ_Hole
  | Typ_Error _       -> []

let is_refl : sub_prf -> bool = fun (_,_,a,b,_) -> strict_eq_kind a b

let mkSchema ?(ord_name="α") schema =
  let ord i = ord_name^"_"^string_of_int i in
  let osnames = Array.init (mbinder_arity schema.sch_judge) ord in
  let os = Array.map (fun s -> OVars s) osnames in
  let osnames = String.concat "," (Array.to_list osnames) in

  let (a,b) = msubst schema.sch_judge os in
  let s = match a with
    | SchKind k -> kind_to_string false k
    | SchTerm t -> term_to_string false (Pos.none (TFixY(None,0,t)))
  in
  let o2s = String.concat ", "
                          (List.map (fun i -> ord i) schema.sch_posit) in
  let arrow = if !latex_mode then "\\Rightarrow" else "=>" in
  let r2s =
    if schema.sch_relat = [] then ""
    else
      String.concat "& "
         (List.map (fun (i,j) -> ord i^"<"^ ord j) schema.sch_relat)
      ^ arrow
  in

  let these = if !latex_mode then "\\vdash" else "|-" in
  sprintf "∀%s (%s %s %s %s : %s)" osnames o2s these r2s s (kind_to_string false b)

let print_schema ?(ord_name="α") ch schema =
  fprintf ch "%s" (mkSchema ~ord_name schema)

let rec typ2proof : Sct.index list -> typ_prf -> string Proof.proof
  = fun used_ind (os,t,k,r) ->
  let open Proof in
  let sub2proof = sub2proof used_ind in
  let typ2proof = typ2proof used_ind in
  let t2s = term_to_string false and k2s = kind_to_string false in
  let mkJudgment os t k =
    let o2s = String.concat ", " (List.map (ordi_to_string false) os) in
    sprintf "%s \\vdash %s : %s" o2s (t2s t) (k2s k)
  in
  let c = mkJudgment os t k in
  let binaryT name c p1 p2 =
    if is_refl p1 then unaryN name c p2
    else binaryN name c (sub2proof p1) p2
  in
  let unaryT name c p1 =
    if is_refl p1 then axiomN name c
    else unaryN name c (sub2proof p1)
  in
  let fn ptr = match !ptr with
  | Todo -> axiomN (sprintf "ERROR(Missing inductive proof)") c
  | Induction(schema,(os,t,a,_,_ as p))  ->
     let c' =
       sprintf (if !latex_mode then "\\H{%s}{%s}"
                else "[%s]_{%s}") (mkSchema schema) (Sct.strInd schema.sch_index)
     in
     let p' = unaryN "\\G" (mkJudgment os t a) (hyp c') in
     if is_refl p then p' else binaryT "" c p p'
  | Unroll(schema,tros,p) ->
     if List.mem schema.sch_index used_ind then (
       let c0 = mkSchema schema in
       unaryN "\\G" c
         (unaryN ("\\I{"^ Sct.strInd schema.sch_index ^"}") c0 (typ2proof p)))
     else (
         ordi_tbl := List.map (fun (o1,o2) -> (o1,(o2,true))) tros @ !ordi_tbl;
         typ2proof p)
  in
  match r with
  | Typ_YGen ptr      -> fn ptr
  | Typ_Coer(p1,p2)   -> if is_refl p1 then typ2proof p2
                         else binaryT "⊆" c p1 (typ2proof p2)
  | Typ_Nope(p)       -> typ2proof p
  | Typ_Defi(p)       -> unaryT "" c p
  | Typ_Prnt(p)       -> unaryT "\\mathrm{Pr}" c p
  | Typ_Cnst(p)       -> unaryT "\\mathrm{Ax}" c p
  | Typ_Func_i(p1,p2) ->
     begin
       match t.elt with
       (* optim for constant constructor in case *)
       | TAbst(_,f) when binder_name f = "" -> typ2proof p2
       | _ -> binaryT "→_i" c p1 (typ2proof p2)
     end
  | Typ_Func_e(p1,p2) -> binaryN "→_e" c (typ2proof p1) (typ2proof p2)
  | Typ_Prod_i(p,ps)  -> n_aryN "×_i" c (sub2proof p :: List.map typ2proof ps)
  | Typ_Prod_e(p)     -> unaryN "×_e" c (typ2proof p)
  | Typ_DSum_i(p1,p2) -> binaryT "+_i" c p1 (typ2proof p2)
  | Typ_DSum_e(p,ps,_)-> n_aryN "+_e" c (typ2proof p :: List.map typ2proof ps) (* FIXME *)
  | Typ_Hole          -> axiomN "AXIOM" c
  | Typ_Error msg     -> axiomN (sprintf "ERROR(%s)" msg) c
  | Typ_Yufl p        -> unaryN "Y" c (typ2proof p)

and     sub2proof : Sct.index list -> sub_prf -> string Proof.proof =
  fun used_ind (os,t,a,b,r) ->
  let open Proof in
  let sub2proof = sub2proof used_ind in
  let t2s = term_to_string true and k2s = kind_to_string false in
  let o2s = String.concat ", " (List.map (ordi_to_string false) os) in
  let c = sprintf "%s \\vdash %s ∈ %s ⊆ %s" o2s (t2s t) (k2s a) (k2s b) in
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
  | Sub_Ind(sch)      -> let p0 = sprintf
                                (if !latex_mode then "\\H{%s}{%s}"
                                 else "[%s]_{%s}")
                                (mkSchema sch) (Sct.strInd sch.sch_index)
                         in
                         unaryN "\\GP" c (hyp p0)
  | Sub_Error(msg)    -> axiomN (sprintf "ERROR(%s)" msg) c
  | Sub_Gen(schema,tros,((os0,t0,_,_,_) as p)) ->
     if List.mem schema.sch_index used_ind then (
       let c0 = mkSchema schema in
       unaryN "\\GP" c
         (unaryN ("\\IP{"^ Sct.strInd schema.sch_index ^"}") c0 (sub2proof p)))
     else (
         ordi_tbl := List.map (fun (o1,o2) -> (o1,(o2,true))) tros @ !ordi_tbl;
         epsilon_term_tbl := (t0,(t,"",-1)) :: !epsilon_term_tbl;
         sub2proof p)

let sub2proof p = sub2proof (sub_used_ind p) p
let typ2proof p = typ2proof (typ_used_ind p) p
let print_typing_proof    ch p = Proof.output ch (typ2proof p)
let print_subtyping_proof ch p = Proof.output ch (sub2proof p)


(****************************************************************************
 *                          Interface functions                             *
 ****************************************************************************)

let print_term ?(unfolded_Y=Some[]) ?(give_pos = false) unfold ff t =
  print_term ~give_pos unfold false unfolded_Y ff t; pp_print_flush ff ()

let print_kind unfold ff t =
  print_kind unfold false None ff t; pp_print_flush ff ()

let kind ff k = print_kind false ff k
let term ff t = print_term false ff t

let _ = fprint_kind := print_kind; fprint_term := print_term

let print_kind_def unfold ff kd =
  pkind_def unfold ff kd; pp_print_flush ff ()

let print_ordi unfold ff o =
  print_ordi unfold None ff o; pp_print_flush ff ()

let print_ordis = print_list (print_ordi false) ","

let print_position ff pos =
  let pos = from_opt (map_opt short_pos_to_string pos) "..." in
  fprintf ff "[%s]" pos; pp_print_flush ff ()

let print_epsilon_tbls ff =
  list_ref_iter (fun (t,(t0,name,index)) ->
    match t.elt with
    | TCnst(f,a,b) when name <> "" ->
       let x = free_of (new_tvari (binder_name f)) in
       let t = subst f x in
       fprintf ff "%s_{%d} &= ε_{%a ∈ %a}(%a ∉ %a)\\\\\n" name index
         (print_term ~unfolded_Y:None false) (Pos.none x) (print_kind false) a
         (print_term ~unfolded_Y:None false) t (print_kind false) b
    | _ when name = "" -> ()
    | _ -> assert false)
    epsilon_term_tbl;
  list_ref_iter (fun (f,(name,index,u,is_exists)) ->
    let x = new_prvar f in
    let k = subst f x in
    let symbol = if is_exists then "∈" else "∉" in
      fprintf ff "%s_{%d} &= ε_{%s}(%a %s %a)\\\\\n" name index
              (binder_name f) (print_term ~unfolded_Y:None false) u symbol
              (print_kind false) k) epsilon_type_tbl;
  list_ref_iter (fun (o,(n,defi)) ->
      if not defi then
        fprintf ff "%a &= %a\\\\\n" (print_ordi false) n
                (print_ordi true) o) ordi_tbl

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
