open Format
open Bindlib
open Util
open Ast
open Print
open Parser
open Raw
open Decap
open Typing

let _ = handle_stop true

let quit    = ref false
let prelude = ref true
let files   = ref ([] : string list)

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
  | End_of_file          -> true
  | Finish               -> true
  | Stopped              -> output.f "Stopped\n%!"; true
  | Unsugar_error(loc,msg)
                         -> output.f "%a:\n%s\n%!" print_position loc msg; false
  | Parse_error(fname,lnum,cnum,_,_)
                         -> output.f "%a:\nSyntax error\n%!" position2 (fname, lnum, cnum); false
  | Unbound(loc,s)       -> output.f "%a:\nUnbound: %s\n%!" print_position loc s; false
  | Type_error(loc, msg)
                         -> output.f "%a:\nType error: %s\n%!" print_position loc msg; false
  | e                    -> output.f "Uncaught exception %s\n%!" (Printexc.to_string e); false

let rec interact () =
  Printf.printf ">> %!";
  ignore (treat_exception (fun () -> toplevel_of_string (read_line ())) ());
  interact ()

let js_object = Js.Unsafe.variable "Object"
let js_handler = jsnew js_object ()
let postMessage = Js.Unsafe.variable "postMessage"

let onmessage event =
  let fname = event##data##fname in
  let args = event##data##args in
  let handle = Js.Unsafe.get js_handler fname in
  let result = Js.Unsafe.fun_call handle (Js.to_array args) in
  let response = jsnew js_object () in
  Js.Unsafe.set response (Js.string "fname") fname;
  Js.Unsafe.set response (Js.string "result") result;
  Js.Unsafe.call postMessage (Js.Unsafe.variable "self") [|Js.Unsafe.inject response|]

let _ = Js.Unsafe.set (Js.Unsafe.variable "self") (Js.string "onmessage") onmessage

let buf = Buffer.create 256
let fbuf = formatter_of_buffer buf

let _ = output.f <- fun format ->
  Buffer.clear buf;
  kfprintf (fun _fbuf ->
    let s = Js.string (Buffer.contents buf) in
    ignore (Js.Unsafe.call postMessage (Js.Unsafe.variable "self") [|Js.Unsafe.inject s|]);
    Buffer.clear buf) fbuf format

let eval_file_string s =
  let s = Js.to_string s in
  let b = treat_exception (parse_string file_contents blank) s in
  if b then Js.string "OK" else Js.string "ERREUR FATALE"

let eval_toplevel_string s =
  Dom_html.window##alert (Js.string "call");
  let s = Js.to_string s in
  let b = treat_exception (parse_string file_contents blank) s in
  if b then Js.string "OK" else Js.string "ERREUR FATALE"

let _ =
  Js.Unsafe.set js_handler (Js.string "eval_file_string") (Js.wrap_callback eval_file_string);
  Js.Unsafe.set js_handler (Js.string "eval_toplevel_string") (Js.wrap_callback eval_toplevel_string)
