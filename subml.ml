open Format
open Bindlib
open Ast
open Print
open Parser
open Raw
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

let rec interact () =
  Printf.printf ">> %!";
  let loop () = toplevel_of_string (read_line ()) in
  if handle_exception loop () then exit 0;
  interact ()

let _ =
  Arg.parse spec add_file "";
  let files = if !prelude then "lib/prelude.typ" :: !files else !files in
  if not (List.for_all (handle_exception eval_file) files) then exit 1;
  if not !quit then interact ()
