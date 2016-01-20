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
  | Stopped              -> io.stderr "Stopped\n%!"; true
  | Unsugar_error(loc,msg)
                         -> io.stderr "%a:\n%s\n%!" print_position loc msg; false
  | Parse_error(fname,lnum,cnum,_,_)
                         -> io.stderr "%a:\nSyntax error\n%!" position2 (fname, lnum, cnum); false
  | Unbound(loc,s)       -> io.stderr "%a:\nUnbound: %s\n%!" print_position loc s; false
  | Type_error(loc, msg)
                         -> io.stderr "%a:\nType error: %s\n%!" print_position loc msg; false
  | e                    -> io.stderr "Uncaught exception %s\n%!" (Printexc.to_string e); false

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
  Js.Unsafe.set response (Js.string "typ") (Js.string "result");
  Js.Unsafe.set response (Js.string "fname") fname;
  Js.Unsafe.set response (Js.string "result") result;
  Js.Unsafe.call postMessage (Js.Unsafe.variable "self") [|Js.Unsafe.inject response|]

let _ = Js.Unsafe.set (Js.Unsafe.variable "self") (Js.string "onmessage") onmessage

let buf = Buffer.create 256
let fbuf = formatter_of_buffer buf

let output = fun chname format ->
  Buffer.clear buf;
  kfprintf (fun _fbuf ->
    let s = Js.string (Buffer.contents buf) in
    let response = jsnew js_object () in
    Js.Unsafe.set response (Js.string "typ") (Js.string chname);
    Js.Unsafe.set response (Js.string "result") s;
    ignore (Js.Unsafe.call postMessage (Js.Unsafe.variable "self") [|Js.Unsafe.inject response|]);
    Buffer.clear buf) fbuf format

let _ = io.stdout <- (fun format -> output "stdout" format)
let _ = io.log    <- (fun format -> output "log"    format)
let _ = io.stderr <- (fun format -> output "stderr" format)

let _ = io.files  <- (fun fname  ->
  let thread = XmlHttpRequest.perform_raw_url fname in
  let res = Lwt.bind thread (fun frame ->
    Lwt.return (Input.buffer_from_string frame.XmlHttpRequest.content);
  )
  in
  match Lwt.state res with
    Lwt.Return buf -> buf
  | Lwt.Fail e     -> raise e
  | Lwt.Sleep      -> assert false)

let eval_file_string s =
  let s = Js.to_string s in
  let b = treat_exception (parse_string file_contents blank) s in
  if b then Js.string "OK" else Js.string "ERREUR"

let eval_toplevel_string s =
  Dom_html.window##alert (Js.string "call");
  let s = Js.to_string s in
  let b = treat_exception (parse_string file_contents blank) s in
  if b then Js.string "OK" else Js.string "ERREUR"

let _ =
  Js.Unsafe.set js_handler (Js.string "eval_file_string") (Js.wrap_callback eval_file_string);
  Js.Unsafe.set js_handler (Js.string "eval_toplevel_string") (Js.wrap_callback eval_toplevel_string)
