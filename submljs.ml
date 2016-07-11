open Format
open Parser
open Io

let js_object = Js.Unsafe.variable "Object"
let postMessage = Js.Unsafe.variable "postMessage"
let syncloadsubmlfile = Js.Unsafe.variable "syncloadsubmlfile"

let onmessage event =
  let filename = Js.to_string event##data##fname in
  let s = Js.to_string event##data##args in
  let b = handle_exception (full_of_string filename) s in
  Io.log "Editor content loaded\n%!";
  let result = if b then Js.string "OK" else Js.string "ERROR" in
  let response = jsnew js_object () in
  Js.Unsafe.set response (Js.string "typ") (Js.string "result");
  Js.Unsafe.set response (Js.string "fname") filename;
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

(* FIXME
let _ =
  let open Io in
  fmts.out <- (fun fmt -> output "stdout" fmt);
  fmts.log <- (fun fmt -> output "log"    fmt);
  fmts.err <- (fun fmt -> output "stderr" fmt)

let _ = io.files  <- (fun filename  ->
  let args = [|Js.Unsafe.inject (Js.string filename)|] in
  let res = Js.Unsafe.fun_call  syncloadsubmlfile args in
  let s = Js.to_string res in
  Input.buffer_from_string ~filename s)
*)

let _ =
  let s = Io.file "lib/prelude.typ" in
  ignore (handle_exception full_of_buffer s);
  Io.log "File \"lib/prelude.typ\" loaded\n%!"
