open Bindlib
open Util
open Ast
open Print
open Dparser

let st = initial_state true

let _ = handle_stop true

let rec interact () =
  let error msg = Printf.eprintf "%s\n%!" msg; interact () in
  Printf.printf ">> %!";
  try toplevel_of_string st (read_line ()); interact () with
  | End_of_file          -> ()
  | Finish               -> ()
  | Stopped              -> error "Stopped."
  | Unsugar_error(_,msg) -> error ("!!! Error: "^msg)
  | Failure("No parse.") -> interact ()
  | e                    -> error (Printexc.to_string e)

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let fn = Sys.argv.(i) in
    Printf.printf "## Loading file %S\n%!" fn;
    eval_file fn st
  done;
  interact ()
