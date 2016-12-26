(****************************************************************************)
(**{3                             LaTeX printing                           }*)
(****************************************************************************)
open Bindlib
open Format
open Ast
open Print
open Position
open Compare
open LibTools

(****************************************************************************
 *                              Proof printing                              *
 ****************************************************************************)

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * kdef
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * Sct.call_table
  | TProof  of typ_prf
  | Sct     of Sct.call_table
  | Witnesses

let rec to_string = function
  | Text(t) -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _       -> assert false

let rec output toplevel ch =
  let output = output false in function
  | Kind(n,ufd,k) -> break_hint := n; print_kind ufd ch k; break_hint := 0
  | Term(n,ufd,t) -> break_hint := n; print_term ufd ch t; break_hint := 0
  | Text(t)       -> fprintf ch "%s" t
  | List(l)       ->
     if toplevel then
       fprintf ch "%a" (fun ch -> List.iter (output ch)) l
     else
       fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  | SProof (p,calls) ->
     let save = !ignore_witness in
     ignore_witness := false;
     print_subtyping_proof ch p;
     fprintf ch "\\begin{center}\n";
     if Sct.is_empty calls then Sct.latex_print_calls ch calls;
     fprintf ch "\\end{center}\n%!";
     ignore_witness := save
  | TProof p      -> print_typing_proof ch p
  | Witnesses     -> print_epsilon_tbls ch; reset_epsilon_tbls ()
  | KindDef(n,t)  ->
     let name = t.tdef_tex_name in
     let f = t.tdef_value in
     let oargs = mbinder_names f in
     let oparams = Array.map (fun s -> free_of (new_ovari s)) oargs in
     let k = msubst f oparams in
     let kargs = mbinder_names k in
     let kparams = Array.map (fun s -> free_of (new_kvari s)) kargs in
     let k = msubst k kparams in
     let print_array ch a =
       if Array.length a = 0 then () else
       fprintf ch "(%s%a)" a.(0) (fun ch a ->
         for i = 1 to Array.length a - 1 do
           fprintf ch ",%s" a.(i)
         done) a
     in
     break_hint := n;
     fprintf ch "%s%a &= %a" name
       print_array (Array.append oargs kargs) (print_kind true) k;
     break_hint := 0
  | Sct calls ->
      Sct.latex_print_calls ch calls

let output ff tex =
  let save_mode = !latex_mode in
  latex_mode := true;
  try
    output true ff tex;
    latex_mode := save_mode
  with e ->
    latex_mode := save_mode;
    raise e

let ignore_latex = ref false

let ordi_to_printer (_,o) =
  (fun ff -> Print.print_ordi false ff o),
  (fun ff ->       print_ordi false ff o)
