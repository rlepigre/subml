open Ast
open Print
open Latex
open Bindlib

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * type_def
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * Sct.calls (* sub_prf * ((int * int) list * Sct.calls) *)
  | TProof  of typ_prf
  | Sct     of Sct.calls (* ((int * int) list * Sct.calls) list *)
  | Witnesses

let rec to_string = function
  | Text(t) -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _       -> assert false

let print_rule_name ff rn =
  let open Printf in
  match rn with
  | NUseInd n -> fprintf ff "H(%d)" n
  | NRefl -> fprintf ff "="
  | NArrow -> fprintf ff "\\to"
  | NSum -> fprintf ff "+"
  | NProd -> fprintf ff "\\times"
  | NAllLeft -> fprintf ff "\\forall_l"
  | NAllRight -> fprintf ff "\\forall_r"
  | NExistsLeft -> fprintf ff "\\exists_l"
  | NExistsRight -> fprintf ff "\\exists_r"
  | NMuLeft (-1) -> fprintf ff "\\mu_l"
  | NMuLeft n -> fprintf ff "\\mu_l(%d)" n
  | NMuRightInf -> fprintf ff "\\mu_r^\\infty"
  | NNuLeftInf -> fprintf ff "\\nu_l^\\infty"
  | NMuRight -> fprintf ff "\\mu_r"
  | NNuLeft -> fprintf ff "\\nu_l"
  | NNuRight (-1) -> fprintf ff "\\nu_r"
  | NNuRight n -> fprintf ff "\\nu_r(%d)" n
  | NProjLeft -> fprintf ff "\\pi_l"
  | NProjRight -> fprintf ff "\\pi_r"
  | NWithLeft -> fprintf ff "w_l"
  | NWithRight -> fprintf ff "w_r"
  | NUnknown -> fprintf ff "?"

let print_calls ch arities calls =
  let print_cmp ch c =
    match c with
    | Sct.Unknown -> Printf.fprintf ch "?"
    | Sct.Less -> Printf.fprintf ch "<"
    | Sct.Leq  -> Printf.fprintf ch "="
  in
  let print_args ch i =
    let a = try List.assoc i arities with Not_found -> assert false in
    for i = 0 to a - 1 do
      Printf.fprintf ch "%sx_%d" (if i = 0 then "" else ",") i
    done
  in
  Printf.fprintf ch "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  List.iter (fun (i,_) ->
    Printf.fprintf ch "    N%d [ label = \"I_%d(%a)\" ];\n" i i print_args i) (List.filter (fun (i,_) ->
       List.exists (fun (j,k,_,_) -> i = j || i =k) calls) arities);
  let print_call arities (i,j,c,a) =
    Printf.fprintf ch "    N%d -> N%d [label = \"(" j i;
    Array.iteri (fun i c ->
      Printf.fprintf ch "%s%ax_%d" (if i = 0 then "" else ",") print_cmp c a.(i)) c;
    Printf.fprintf ch ")\"]\n%!"
  in
  List.iter (print_call arities) calls;
  Printf.fprintf ch "  }\n\\end{dot2tex}\n"

(*
let print_subtyping_proof, print_typing_proof =
  let rec fn ch (p:sub_proof) =
    let rn, strees = Print_trace.filter_rule p in
    let strees =
      let r = List.filter (fun p -> not (eq_kind p.left p.right)) strees in
      if r = [] then strees else r
    in
    List.iter (fn ch) strees;
    let cmd = match List.length strees with
      | 0 -> "\\AxiomC{}\n\\UnaryInfC"
      | 1 -> "\\UnaryInfC"
      | 2 -> "\\BinaryInfC"
      | 3 -> "\\TrinaryInfC"
      | _ -> assert false
    in
    if !print_term_in_subtyping then
      Printf.fprintf ch "\\RightLabel{$%a$}%s{$%a \\in %a \\subset %a$}\n%!" print_rule_name rn cmd
	(print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right
    else
      Printf.fprintf ch "\\RightLabel{$%a$}%s{$%a \\subset %a$}\n%!" print_rule_name rn cmd
	(print_kind false) p.left (print_kind false) p.right
            (*Printf.fprintf ch "%s{$%a \\in %a \\subset %a$}\n%!" cmd
	      (print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right*)

  and gn ch (p:typ_proof) =
    let strees = List.filter (fun p -> not (eq_kind p.left p.right)) p.strees in
    let cmd = match List.length strees + List.length p.ttrees with
      | 0 -> "\\AxiomC{}\n\\UnaryInfC"
      | 1 -> "\\UnaryInfC"
      | 2 -> "\\BinaryInfC"
      | 3 -> "\\TrinaryInfC"
      | _ -> assert false
    in
    List.iter (fn ch) strees;
    List.iter (gn ch) p.ttrees;
    Printf.fprintf ch "%s{$%a : %a$}\n%!" cmd
      (print_term false) p.tterm (print_kind false) p.typ
  in
  (fun ch p -> fn ch p),
  (fun ch p -> gn ch p)

let rec output ch = function
  | Kind(n,unfold,k) -> break_hint := n; print_kind unfold ch k; break_hint := 0
  | Term(n,unfold,t) -> break_hint := n; print_term unfold ch t; break_hint := 0
  | Text(t)        -> Printf.fprintf ch "%s" t
  | List(l)        -> Printf.fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  | SProof (p,(tt,sct)) ->
     Printf.fprintf ch "\\begin{prooftree}\n";
     print_subtyping_proof ch p;
     Printf.fprintf ch "\\end{prooftree}\n%!";
     Printf.fprintf ch "\\begin{center}\n";
     if sct <> [] then print_calls ch tt sct;
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
  | Sct ls ->
     List.iter (fun (tt,calls) -> print_calls ch tt calls) ls
*)
