(****************************************************************************)
(**{3                             LaTeX printing                           }*)
(****************************************************************************)
open Bindlib
open Format
open Ast
open Print
open Pos
open LibTools
open Raw

(****************************************************************************
 *                              Proof printing                              *
 ****************************************************************************)

type latex_output =
  | Kind    of int * bool * pkind
  | KindDef of int * string loc
  | Term    of int * bool * pterm
  | KindOf  of int * string loc
  | Text    of string
  | List    of latex_output list
  | SProof  of pkind * pkind
  | TProof  of int * strloc (* name of value *)
  | Sch     of string loc * string loc * int * string
  | Sct     of string loc
  | Witnesses

let search_schemas name p =
  let res = ref [] in

  let rec fn ptr = match !ptr with
    | Unroll(sch,_,p) ->
       (try
         let osnames = Array.init (mbinder_arity sch.sch_judge)
                           (fun i -> "α_"^string_of_int i) in
         let os = Array.map (fun s -> OVars s) osnames in
         let (a,_) = msubst sch.sch_judge os in
         match a with
         | SchTerm f when binder_name f = name -> res := sch :: !res
         | _ -> raise Not_found
        with Not_found -> ());
        gn p
    | _ -> ()

  and gn (_, _, _, r) =
    match r with
    | Typ_YGen ptr -> fn ptr
    | Typ_Coer   (_, p)
    | Typ_Func_i (_, p)
    | Typ_DSum_i (_, p)
    | Typ_Nope   p
    | Typ_Yufl   p
    | Typ_Prod_e p        -> gn p

    | Typ_Func_e (p1, p2) -> gn p1; gn p2

    | Typ_Prod_i (_, ps)  -> List.iter gn ps
    | Typ_DSum_e (p, ps, None)
                          -> gn p; List.iter gn ps
    | Typ_DSum_e (p, ps, Some po)
                          -> gn p; List.iter gn ps; gn po

    | Typ_Abrt
    | Typ_Defi  _
    | Typ_Prnt  _
    | Typ_Cnst  _
    | Typ_Error _  -> ()
  in
  gn p; !res

let rec to_string = function
  | Text(t) -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _       -> assert false

let rec output toplevel ch =
  let output = output false in function
  | Kind(n,ufd,k) -> let k = unbox (unsugar_kind empty_env k) in
                     break_hint := n; print_kind ufd ch k; break_hint := 0
  | Term(n,ufd,t) -> let t = unbox (unsugar_term empty_env t) in
                     break_hint := n; print_term ufd ch t; break_hint := 0
  | Text(t)       -> fprintf ch "%s" t
  | List(l)       ->
     if toplevel then
       fprintf ch "%a" (fun ch -> List.iter (output ch)) l
     else
       fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  | SProof (a,b) ->
     let save = !ignore_witness in
     ignore_witness := false;
     let a = unbox (unsugar_kind empty_env a) in
     let b = unbox (unsugar_kind empty_env b) in
     let (prf, calls) = Typing.subtype None a b in
     print_subtyping_proof ch prf;
     fprintf ch "\\begin{center}\n";
     if Sct.is_empty calls then Sct.latex_print_calls ch calls;
     fprintf ch "\\end{center}\n%!";
     ignore_witness := save
  | TProof(_,id) ->
      begin
        try print_typing_proof ch (Hashtbl.find val_env id.elt).proof
        with Not_found -> raise(Unbound(id.elt, id.pos))
      end
  | Witnesses     -> print_epsilon_tbls ch; reset_epsilon_tbls ()
  | KindOf(n,id)  ->
     let t =
       try
         Hashtbl.find val_env id.elt
       with
         Not_found -> raise (Unbound(id.elt,id.pos))
     in
     break_hint := n; print_kind false ch t.ttype; break_hint := 0
  | KindDef(_,id)  ->
     let t =
       try
         Hashtbl.find typ_env id.elt
       with
         Not_found -> raise (Unbound(id.elt,id.pos))
     in
     let name = t.tdef_tex_name in
     let f = t.tdef_value in
     let oargs = mbinder_names f in
     let oparams = Array.map (fun s -> mk_free_o (new_ovari s)) oargs in
     let k = msubst f oparams in
     let kargs = mbinder_names k in
     let kparams = Array.map (fun s -> mk_free_k (new_kvari s)) kargs in
     let k = msubst k kparams in
     let fmt :('a,'b,'c,'d) format4 = match oargs, kargs with
       [||], [||] -> "%s%a%a &= %a"
     | [||], _    -> "%s%a(%a) &= %a"
     |  _  , [||] -> "%s_{%a}%a &= %a"
     |  _         -> "%s_{%a}(%a) &= %a"
     in
     fprintf ch fmt name
       (print_strarray ",") oargs (print_strarray ",") kargs (print_kind true) k;
     break_hint := 0
  | Sct id ->
     let calls =
       try
         (Hashtbl.find val_env id.elt).calls_graph
       with
         Not_found -> raise (Unbound(id.elt,id.pos))
     in
     Sct.latex_print_calls ch calls
  | Sch (id,name,i,ord_name) ->
     let prf =
       try
         (Hashtbl.find val_env id.elt).proof
       with Not_found -> raise (Unbound(id.elt,id.pos))
     in
     let schemas =
       try
         search_schemas name.elt prf
       with Not_found -> raise (Unbound(name.elt, name.pos))
     in
     let sch = List.nth schemas i in
     print_schema ~ord_name ch sch

let output ff tex =
  let save_mode = !print_mode in
  print_mode := TeX;
  try
    output true ff tex;
    print_mode := save_mode
  with e ->
    print_mode := save_mode;
    raise e

let ignore_latex = ref false

let ordi_to_printer (_,o) =
  (fun ff -> Print.print_ordi false ff o),
  (fun ff ->       print_ordi false ff o)
