open Bindlib
open Util
open Ast
open Multi_print
open Dparser

let _ = handle_stop true

let quit = ref false

let spec =
  [ ("--latex", Arg.Unit (fun _ -> print_mode := Latex), "Activate latex mode");
    ("--verbose", Arg.Set verbose, "Activate verbose mode");
    ("--debug", Arg.Set Typing.debug, "Activate verbose mode");
    ("--no-contraction", Arg.Clear Ast.contract_mu, "Activate verbose mode");
    ("--debug-sct", Arg.Set Sct.debug_sct, "Activate sct verbose mode");
    ("--show-leq", Arg.Set Print.show_leq, "Print inductive ordinals with <= constraints");
    ("--tex-file", Arg.String (fun s -> open_latex s), "Choose tex file output");
    ("--quit", Arg.Set quit, "quit after parsing files");
  ]

let rec interact () =
  let error msg = Printf.eprintf "%s\n%!" msg; interact () in
  Printf.printf ">> %!";
  try toplevel_of_string (read_line ()); interact () with
  | End_of_file          -> ()
  | Finish               -> ()
  | Stopped              -> error "Stopped."
  | Unsugar_error(_,msg) -> error ("!!! Error: "^msg)
  | Failure("No parse.") -> interact ()
  | e                    -> error (Printexc.to_string e)

let _ =
  Arg.parse spec (fun fn -> eval_file fn) "";
  if not !quit then interact ()
