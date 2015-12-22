open Ast
open Print
open Latex
open Trace

type latex_output =
  | Kind of (bool * kind)
  | Term of (bool * term)
  | Text of string
  | List of latex_output list
  | SProof of sub_proof
  | TProof of typ_proof
  | Ordinals

let rec to_string = function
  | Text t -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _ -> assert false

let print_subtyping_proof, print_typing_proof =
  let rec fn ch (p:sub_proof) =
    match !(p.unused) with
      | None ->
       let cmd = match List.length p.strees with
	 | 0 -> "\\AxiomC{}\n\\UnaryInfC"
	 | 1 -> "\\UnaryInfC"
	 | 2 -> "\\BinaryInfC"
	 | 3 -> "\\TernaryInfC"
	 | _ -> assert false
       in
       List.iter (fn ch) p.strees;
       Printf.fprintf ch "%s{$%a \\subset %a$}\n%!" cmd
	 (print_kind false) p.left (print_kind false) p.right
       (*Printf.fprintf ch "%s{$%a \\in %a \\subset %a$}\n%!" cmd
	 (print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right*)
    | Some o ->
       ignored_ordinals := o :: !ignored_ordinals;
      List.iter (fn ch) p.strees;
  and gn ch (p:typ_proof) =
    let subs =
      (*List.filter (fun p -> not (lower_kind p.left p.right))*) p.strees
    in
    let cmd = match List.length subs + List.length p.ttrees with
      | 0 -> "\\AxiomC{}\n\\UnaryInfC"
      | 1 -> "\\UnaryInfC"
      | 2 -> "\\BinaryInfC"
      | 3 -> "\\TernaryInfC"
      | _ -> assert false
    in
    List.iter (fn ch) subs;
    List.iter (gn ch) p.ttrees;
    Printf.fprintf ch "%s{$%a : %a$}\n%!" cmd
      (print_term false) p.tterm (print_kind false) p.typ
  in
  (fun ch p -> fn ch p; ignored_ordinals := []),
  (fun ch p -> gn ch p; ignored_ordinals := [])

let rec output ch = function
  | Kind(unfold,k) -> print_kind unfold ch k
  | Term(unfold,t) -> print_term unfold ch t
  | Text(t)        -> Printf.fprintf ch "%s" t
  | List(l)        -> Printf.fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  | SProof p       -> print_subtyping_proof ch p
  | TProof p       -> print_typing_proof ch p
  | Ordinals       -> print_reset_ordinals ch
