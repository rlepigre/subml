open Bindlib
open Util
open Ast
open Print
open Dparser

let st = initial_state ()

let rec interact () =
  let error msg = Printf.eprintf "!!! Error: %s\n%!" msg; interact () in
  Printf.printf ">> %!";
  try command_of_string st (read_line ()); interact () with
  | End_of_file          -> ()
  | Unsugar_error(_,msg) -> error msg
  | Failure("No parse.") -> interact ()
  | e                    -> error (Printexc.to_string e)

let _ = interact ()
