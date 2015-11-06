open Bindlib
open Util
open Ast
open Print
open Dparser

let st = initial_state ()

let _ = handle_stop true

let rec interact () =
  let error msg = Printf.eprintf "%s\n%!" msg; interact () in
  Printf.printf ">> %!";
  try command_of_string st (read_line ()); interact () with
  | End_of_file          -> ()
  | Finish               -> ()
  | Stopped              -> error "Stopped."
  | Unsugar_error(_,msg) -> error ("!!! Error: "^msg)
  | Failure("No parse.") -> interact ()
  | e                    -> error (Printexc.to_string e)

let _ = interact ()
