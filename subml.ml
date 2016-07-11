open Format
open Bindlib
open Ast
open Print
open Parser
open Raw
open Decap
open Typing
open Type
open Position
open System

let _ = handle_stop true

let quit    = ref false
let prelude = ref true
let files   = ref []

let add_file fn = files := !files @ [fn]

let spec =
  [ ( "--verbose"
    , Arg.Set verbose
    , "Activate verbose mode" )
  ; ( "--debug"
    , Arg.Set Ast.debug
    , "Activate verbose mode" )
  ; ( "--no-contraction"
    , Arg.Clear contract_mu
    , "Activate verbose mode" )
  ; ( "--debug-sct"
    , Arg.Set Sct.debug_sct
    , "Activate sct verbose mode" )
  ; ( "--tex-file"
    , Arg.String Io.(fun s -> fmts.tex <- fmt_of_file s)
    , "Choose tex file output" )
  ; ( "--out-file"
    , Arg.String Io.(fun s -> fmts.out <- fmt_of_file s)
    , "Choose output file" )
  ; ( "--err-file"
    , Arg.String Io.(fun s -> fmts.err <- fmt_of_file s)
    , "Choose error file output" )
  ; ( "--log-file"
    , Arg.String Io.(fun s -> fmts.log <- fmt_of_file s)
    , "Choose log file output" )
  ; ( "--no-prelude"
    , Arg.Clear prelude
    , "Do not load the prelude" )
  ; ( "--no-inline"
    , Arg.Clear Sct.do_inline
    , "Do not optimize call graph by inlining" )
  ; ( "--fixpoint-depth"
    , Arg.Set_int Typing.fixpoint_depth
    , "Depth for termination of recursitve function (default 3)" )
  ; ( "--quit"
    , Arg.Set quit
    , "quit after parsing files" )
  ]

let handle_exception fn v =
  let position2 ff (fname, lnum, cnum) =
    fprintf ff "File %S, line %d, characters %d-%d" fname lnum cnum cnum
  in
  try
    fn v; true
  with
  | End_of_file          -> exit 0
  | Stopped              -> Io.err "Stopped\n%!"; true
  | Arity_error(loc,msg) -> Io.err "%a:\n%s\n%!" print_position loc msg; false
  | Positivity_error(loc,msg) -> Io.err "%a:\n%s\n%!" print_position loc msg; false
  | Parse_error(fname,lnum,cnum,_,_)
                         -> Io.err "%a:\nSyntax error\n%!" position2 (fname, lnum, cnum); false
  | Unbound(s)           -> Io.err "%a:\nUnbound: %s\n%!" print_position s.pos s.elt; false
  | Type_error(loc, msg) -> Io.err "%a:\nType error: %s\n%!" print_position loc msg; false
  | e                    -> Io.err "Uncaught exception %s\n%!" (Printexc.to_string e); exit 1

let rec interact () =
  Printf.printf ">> %!";
  let line = read_line () in
  ignore (handle_exception (fun () -> toplevel_of_string line) ());
  interact ()

let _ =
  Arg.parse spec add_file "";
  let files = if !prelude then "lib/prelude.typ" :: !files else !files in
  if not (List.for_all (handle_exception eval_file) files) then exit 1;
  if not !quit then ignore (handle_exception interact ())
