open Ast
open Print


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

let trace_subtyping ?(ordinal=[]) t k1 k2 =
  let prf = {
    sterm = t;
    left = k1;
    right = k2;
    unused = ordinal;
    strees = [];
    rule_name = NUnknown;
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
  (fun () -> prf.unused <- [])

let trace_sub_pop rn =
  match !trace_state with
  | [SubTyping prf] -> prf.rule_name <- rn; trace_state := [EndSubTyping prf]
  | SubTyping prf::s -> prf.rule_name <- rn;  trace_state := s
  | _ -> assert false

let trace_typ_pop () =
  match !trace_state with
  | [Typing prf] -> trace_state := [EndTyping prf]
  | Typing prf::s -> trace_state := s
  | _ -> assert false

let collect_typing_proof () =
  match !trace_state with
  | [EndTyping prf] -> trace_state := []; prf
  | _ -> assert false

let collect_subtyping_proof () =
  match !trace_state with
  | [EndSubTyping prf] -> trace_state := [] ; prf
  | _ -> assert false

let trace_backtrace () =
  let rec fn = function
    | (Typing p | EndTyping p)::l ->
       Printf.eprintf "%a : %a\n%!"
	 (print_term false) p.tterm (print_kind false) p.typ;
      fn l
    | (SubTyping p | EndSubTyping p)::l ->
       Printf.eprintf "%a ∈ %a ⊆ %a\n%!"
	 (print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right;
      fn l
    | [] -> ()
  in
  fn !trace_state; reset_ordinals (); trace_state := []
