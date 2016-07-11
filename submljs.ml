open Format
open Parser
open Io

let js_object = Js.Unsafe.variable "Object"
let js_self   = Js.Unsafe.variable "self"
let post_msg  = Js.Unsafe.variable "postMessage"
let syncload  = Js.Unsafe.variable "syncloadsubmlfile"

let onmessage event =
  let fname = Js.to_string event##data##fname in
  let args = Js.to_string event##data##args in
  let res = handle_exception (full_of_string fname) args in
  Io.log "Editor content loaded\n%!";
  let result = Js.string (if res then "OK" else "ERROR") in
  let response = jsnew js_object () in
  Js.Unsafe.set response (Js.string "typ")    (Js.string "result");
  Js.Unsafe.set response (Js.string "fname")  fname;
  Js.Unsafe.set response (Js.string "result") result;
  let arg = Js.Unsafe.inject response in
  Js.Unsafe.call post_msg js_self [|arg|]

let output : string -> formatter = fun chname ->
  let buf = Buffer.create 256 in
  let out = Buffer.add_substring buf in
  let flush () =
    let s = Buffer.contents buf in
    Buffer.clear buf;
    let response = jsnew js_object () in
    Js.Unsafe.set response (Js.string "typ") (Js.string chname);
    Js.Unsafe.set response (Js.string "result") (Js.string s);
    ignore (Js.Unsafe.call post_msg js_self [|Js.Unsafe.inject response|])
  in
  make_formatter out flush


(*
let _ = io.files  <- (fun filename  ->
  let args = [|Js.Unsafe.inject (Js.string filename)|] in
  let res = Js.Unsafe.fun_call  syncload args in
  let s = Js.to_string res in
  Input.buffer_from_string ~filename s)
*)


let _ =
  (* Setup the IO stuff. *)
  fmts.out <- output "stdout";
  fmts.err <- output "stderr";
  fmts.log <- output "log";
  fmts.tex <- output "tex";
  (* FIXME file stuff *)
  (* Register callback. *)
  Js.Unsafe.set js_self (Js.string "onmessage") onmessage;
  (* Load the prelude. *)
  ignore (handle_exception full_of_buffer (Io.file "lib/prelude.typ"));
  Io.log "File \"lib/prelude.typ\" loaded\n%!"
