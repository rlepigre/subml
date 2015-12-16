open Ast
open Print

type sub_proof =
  { sterm : term;
    left : kind;
    right : kind;
    unused : ordinal option ref;
    mutable strees : sub_proof list }

type typ_proof =
  { tterm : term;
    typ : kind;
    mutable strees : sub_proof list;
    mutable ttrees : typ_proof list;
  }

type trace_state =
  | Typing of typ_proof
  | SubTyping of sub_proof
  | EndTyping of typ_proof
  | EndSubTyping of sub_proof

let trace_state = ref []

let trace_typing t k =
  let prf = {
    tterm = t;
    typ = k;
    strees = [];
    ttrees = [];
  } in
  match !trace_state with
  | Typing (p)::_ as l ->
     p.ttrees <- prf :: p.ttrees;
     trace_state := Typing prf :: l
  | [] ->
     trace_state := Typing prf :: []
  | _ -> assert false

let trace_subtyping ?ordinal t k1 k2 =
  let unused = ref ordinal in
  let prf = {
    sterm = t;
    left = k1;
    right = k2;
    unused;
    strees = [];
  } in
  (match !trace_state with
  | Typing (p)::_ as l ->
     p.strees <- prf :: p.strees;
     trace_state := SubTyping prf :: l
  | SubTyping (p)::_ as l ->
     p.strees <- prf :: p.strees;
     trace_state := SubTyping prf :: l
  | [] ->
     trace_state := SubTyping prf :: []
  | _ -> assert false);
  (fun () -> unused := None)

let trace_pop () =
  match !trace_state with
  | [Typing prf] -> trace_state := [EndTyping prf]
  | [SubTyping prf] -> trace_state := [EndSubTyping prf]
  | _::s -> trace_state := s
  | [] -> assert false

let collect_typing_proof () =
  match !trace_state with
  | [EndTyping prf] -> trace_state := []; prf
  | _ -> assert false

let collect_subtyping_proof () =
  match !trace_state with
  | [EndSubTyping prf] -> trace_state := [] ; prf
  | _ -> assert false

let print_subtyping_proof, print_typing_proof =
  let rec fn indent (p:sub_proof) =
    match !(p.unused) with
    | None ->
      List.iter (fn (indent^"  ")) p.strees;
      Printf.eprintf "%s%a ∈ %a ⊆ %a\n%!" indent
	print_term p.sterm (print_kind false) p.left (print_kind false) p.right
    | Some o ->
      ignored_ordinals := o :: !ignored_ordinals;
      Printf.eprintf "ignored\n%!";
      List.iter (fn indent) p.strees;
  and gn indent (p:typ_proof) =
    List.iter (fn (indent^"  ")) p.strees;
    List.iter (gn (indent^"  ")) p.ttrees;
    Printf.eprintf "%s%a : %a\n%!" indent
      print_term p.tterm (print_kind false) p.typ
  in
  (fun p -> fn "" p; ignored_ordinals := []),
  (fun p -> gn "" p; ignored_ordinals := [])

let trace_backtrace () =
  let rec fn = function
    | (Typing p | EndTyping p)::l ->
       Printf.eprintf "%a : %a\n%!"
	 print_term p.tterm (print_kind false) p.typ;
      fn l
    | (SubTyping p | EndSubTyping p)::l ->
       Printf.eprintf "%a ∈ %a ⊆ %a\n%!"
	 print_term p.sterm (print_kind false) p.left (print_kind false) p.right;
      fn l
    | [] -> ()
  in
  fn !trace_state; trace_state := []
