open Bindlib
open Util
open Ast
open Print
open Dparser
open Raw
open Decap
open Typing

let _ = handle_stop true

let quit    = ref false
let prelude = ref true
let files   = ref []

let add_file fn = files := !files @ [fn]

let spec =
  [ ("--verbose", Arg.Set verbose, "Activate verbose mode");
    ("--debug", Arg.Set Typing.debug, "Activate verbose mode");
    ("--no-contraction", Arg.Clear Ast.contract_mu, "Activate verbose mode");
    ("--debug-sct", Arg.Set Sct.debug_sct, "Activate sct verbose mode");
    ("--simple-ordinals", Arg.Set Print.simplified_ordinals, "Print inductive ordinals with <= constraints");
    ("--tex-file", Arg.String (fun s -> open_latex s), "Choose tex file output");
    ("--no-prelude", Arg.Clear prelude, "Do not load the prelude");
    ("--quit", Arg.Set quit, "quit after parsing files");
  ]

let treat_exception fn a =
  let position2 fname lnum cnum =
    Printf.eprintf "File %S, line %d, characters %d-%d:" fname lnum cnum cnum
  in
  let error msg = Printf.eprintf "%s\n%!" msg in
  try
    fn a; true
  with
  | End_of_file          -> false
  | Finish               -> false
  | Stopped              -> error "Stopped."; true
  | Unsugar_error(loc,msg)
                         -> print_position stderr loc; error msg; false
  | Parse_error(fname,lnum,cnum,_,_)
                         -> position2 fname lnum cnum; error "Syntax error"; false
  | Unbound(loc,s)       -> print_position stderr loc; error ("Unbound: "^s); false
  | Type_error(loc, msg)
                         -> print_position stderr loc; error ("Type error: "^msg); false
  | e                    -> error (Printexc.to_string e); exit 1

let rec interact () =
  Printf.printf ">> %!";
  ignore (treat_exception toplevel_of_string (read_line ())); interact ()

let _ =
  Arg.parse spec add_file "";
  if !prelude && not (treat_exception eval_file "lib/prelude.typ") then exit 1;
  if List.for_all (treat_exception eval_file) !files && not !quit then interact () else exit 1
