open Format
open Bindlib
open Util
open Ast
open Print
open Parser
open Raw
open Decap
open Typing
open Io

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
  let position2 ff (fname, lnum, cnum) =
    fprintf ff "File %S, line %d, characters %d-%d" fname lnum cnum cnum
  in
  try
    fn a; true
  with
  | End_of_file          -> exit 0
  | Finish               -> exit 0
  | Stopped              -> io.stderr "Stopped\n%!"; true
  | Unsugar_error(loc,msg)
                         -> io.stderr "%a:\n%s\n%!" print_position loc msg; false
  | Parse_error(fname,lnum,cnum,_,_)
                         -> io.stderr "%a:\nSyntax error\n%!" position2 (fname, lnum, cnum); false
  | Unbound(loc,s)       -> io.stderr "%a:\nUnbound: %s\n%!" print_position loc s; false
  | Type_error(loc, msg)
                         -> io.stderr "%a:\nType error: %s\n%!" print_position loc msg; false
  | e                    -> io.stderr "Uncaught exception %s\n%!" (Printexc.to_string e); exit 1

let rec interact () =
  Printf.printf ">> %!";
  ignore (treat_exception (fun () -> toplevel_of_string (read_line ())) ());
  interact ()

let _ =
  Arg.parse spec add_file "";
  if !prelude && not (treat_exception eval_file "lib/prelude.typ") then exit 1;
  if not (List.for_all (treat_exception eval_file) !files) then exit 1;
  if not !quit then interact ()