open Bindlib
open Util
open Ast
open Multi_print
open Dparser

let st = initial_state false

let _ = handle_stop true

let quit = ref false

let spec =
  [ ("--latex", Arg.Unit (fun _ -> print_mode := Latex), "Activate latex mode");
    ("--verbose", Arg.Unit (fun _ -> st.verbose <- true), "Activate verbose mode");
    ("--tex-file", Arg.String (fun s -> open_latex s), "Choose tex file output");
    ("--quit", Arg.Set quit, "quit after parsing files");
  ]

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
  Arg.parse spec (fun fn -> eval_file fn st) "";
  if not !quit then interact ()
