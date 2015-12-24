open Ast
open Trace
open Typing
open Print

let print_subtyping_proof, print_typing_proof =
  let rec fn indent (p:sub_proof) =
    match !(p.unused) with
    | None ->
      List.iter (fn (indent^"  ")) p.strees;
      Printf.eprintf "%s%a ∈ %a ⊆ %a\n%!" indent
	(print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right
    | Some o ->
      ignored_ordinals := o :: !ignored_ordinals;
      Printf.eprintf "ignored\n%!";
      List.iter (fn indent) p.strees;
  and fnopt indent (p:sub_proof) =
    if not (lower_kind p.left p.right) then fn indent p
  and gn indent (p:typ_proof) =
    List.iter (fnopt (indent^"  ")) p.strees;
    List.iter (gn (indent^"  ")) p.ttrees;
    Printf.eprintf "%s%a : %a\n%!" indent
      (print_term false) p.tterm (print_kind false) p.typ
  in
  (fun p -> fn "" p; ignored_ordinals := []),
  (fun p -> gn "" p; ignored_ordinals := [])
