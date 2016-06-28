open Ast
open Print
open Format
open Io

type prf_trace_state =
  | Typing of typ_proof
  | SubTyping of sub_proof
  | EndTyping of typ_proof
  | EndSubTyping of sub_proof

type trace_state =
  { mutable proof : prf_trace_state list;
    mutable calls : ((int * int) list * Sct.calls) list }

let trace_state =
  { proof = []; calls = [] }

let reset st = st.proof <- []; st.calls <- []

let trace_typing t k =
  let prf = {
    tterm = t;
    typ = k;
    strees = [];
    ttrees = [];
  } in
  match trace_state.proof with
  | Typing (p)::_ as l ->
     p.ttrees <- prf :: p.ttrees;
     trace_state.proof <- Typing prf :: l
  | SubTyping (p)::_ as l ->
     trace_state.proof <- Typing prf :: l
  | [] ->
     trace_state.proof <- Typing prf :: []
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
  (match trace_state.proof with
  | Typing (p)::_ as l ->
     p.strees <- prf :: p.strees;
     trace_state.proof <- SubTyping prf :: l
  | SubTyping (p)::_ as l ->
     p.strees <- prf :: p.strees;
     trace_state.proof <- SubTyping prf :: l
  | [] ->
     trace_state.proof <- SubTyping prf :: []
  | _ -> assert false);
  (fun () -> prf.unused <- [])

let trace_sub_pop rn =
  match trace_state.proof with
  | [SubTyping prf] -> prf.rule_name <- rn; trace_state.proof <- [EndSubTyping prf]
  | SubTyping prf::s -> prf.rule_name <- rn;  trace_state.proof <- s
  | _ -> assert false

let trace_get_pop () =
  match trace_state.proof with
  | [SubTyping prf] -> trace_state.proof <- [EndSubTyping prf]; prf
  | SubTyping prf::s -> trace_state.proof <- s; prf
  | _ -> assert false

let trace_restore prf =
  trace_state.proof <- SubTyping prf :: trace_state.proof

let trace_typ_pop () =
  match trace_state.proof with
  | [Typing prf] -> trace_state.proof <- [EndTyping prf]
  | Typing prf::s -> trace_state.proof <- s
  | SubTyping prf::s -> trace_state.proof <- s
  | _ -> assert false

let collect_typing_proof () =
  match trace_state.proof with
  | [EndTyping prf] ->
     let sct = trace_state.calls in
     reset trace_state;
     prf, sct
  | _ -> assert false

let collect_subtyping_proof () =
  match trace_state.proof with
  | [EndSubTyping prf] ->
     let sct = trace_state.calls in
     reset trace_state;
     prf, sct
  | _ -> assert false

let trace_backtrace () =
  let rec fn = function
    | (Typing p | EndTyping p)::l ->
       io.stdout "%a : %a\n%!"
	 (print_term false) p.tterm (print_kind false) p.typ;
      fn l
    | (SubTyping p | EndSubTyping p)::l ->
       io.stdout "%a ∈ %a ⊆ %a\n%!"
	 (print_term false) p.sterm (print_kind false) p.left (print_kind false) p.right;
      fn l
    | [] -> ()
  in
  fn trace_state.proof; reset_epsilon_tbls (); trace_state.proof <- []
