open Earley_core
open Format
open Parser
open Io

open Js_of_ocaml

let js_object = Js.Unsafe.pure_js_expr "Object"
let js_self   = Js.Unsafe.pure_js_expr "self"
let post_msg  = Js.Unsafe.pure_js_expr "postMessage"
let syncload  = Js.Unsafe.pure_js_expr "syncloadsubmlfile"

let onmessage event =
  let fname = Js.to_string event##.data##.fname in
  let args = Js.to_string event##.data##.args in
  if handle_exception (eval_string fname) args then
    Io.log "(* [LOG] Editor content loaded. *)\n%!"
  else
    Io.log "(* [LOG] AN ERROR OCCURED! *)\n%!"

let output : string -> formatter = fun chname ->
  let buf = Buffer.create 256 in
  let out = Buffer.add_substring buf in
  let flush () =
    let s = Buffer.contents buf in
    Buffer.clear buf;
    let response =
      object%js
        val typ = Js.string chname
        val result = Js.string s
      end
    in
    ignore (Js.Unsafe.call post_msg js_self [|Js.Unsafe.inject response|])
  in
  make_formatter out flush

let input : string -> Input.buffer = fun filename ->
  let filename = Filename.concat "lib/" filename in
  let args = [|Js.Unsafe.inject (Js.string filename)|] in
  let res = Js.to_string (Js.Unsafe.fun_call syncload args) in
  Input.from_string ~filename res

let _ =
  Ast.verbose := true;
  Print.show_occur := false;
  (* Setup the IO stuff. *)
  fmts.out <- output "stdout";
  fmts.err <- output "stderr";
  fmts.log <- output "log";
  fmts.tex <- output "tex";
  Io.read_file := input;
  (* Register callback. *)
  Js.Unsafe.set js_self (Js.string "onmessage") onmessage;
  (* Print a message. *)
  Io.log "(* [LOG] Ready! *)\n%!"
