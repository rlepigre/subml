open Ast
open Proof_trace
open Typing
open Print
open Io

let rec filter_rule p =
  match p.unused with
  | [] ->
     p.rule_name, p.strees
  | os ->
     ignored_ordinals := os @ !ignored_ordinals;
    match p.strees with
    | [p'] -> filter_rule p'
    | _ -> assert false

let print_subtyping_proof, print_typing_proof =
  let rec fn indent (p:sub_proof) =
    let rn, strees = filter_rule p in
      List.iter (fn (indent^"  ")) strees;
      io.stdout "%s%a ∈ %a ⊆ %a\n%!" indent
	(print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right
  and fnopt indent (p:sub_proof) =
    if not (lower_kind p.left p.right) then fn indent p
  and gn indent (p:typ_proof) =
    List.iter (fnopt (indent^"  ")) p.strees;
    List.iter (gn (indent^"  ")) p.ttrees;
    io.stdout "%s%a : %a\n%!" indent
      (print_term false) p.tterm (print_kind false) p.typ
  in
  (fun p -> fn "" p),  (fun p -> gn "" p)
