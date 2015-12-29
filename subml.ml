open Bindlib
open Util
open Ast
open Multi_print
open Dparser
open Raw
open Decap

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
  try toplevel_of_string (read_line ()); interact ()
  with
  | End_of_file          -> ()
  | Finish               -> ()
  | Stopped              -> error "Stopped."
  | Unsugar_error(loc,msg) -> error ("!!! Error: "^msg^" at "^string_of_int loc.Location.loc_start.Lexing.pos_lnum)
  | Failure("No parse.") -> interact ()
  | Parse_error _ as e   -> print_exception e; interact ()
  | Unbound(loc,s)       -> error ("Unbound: "^s^" at "^string_of_int loc.Location.loc_start.Lexing.pos_lnum)
  | e                    -> error (Printexc.to_string e)

let _ =
  begin
    let error msg = Printf.eprintf "%s\n%!" msg; exit 1 in
    try
      Arg.parse spec (fun fn -> eval_file fn) "";
    with
    | Stopped              -> error ("Stopped.")
    | Unsugar_error(loc,msg) -> error ("!!! Error: "^msg^
					  " at "^string_of_int loc.Location.loc_start.Lexing.pos_lnum)
    | Failure("No parse.") -> exit 1
    | Parse_error _ as e   -> print_exception e; exit 1
    | Unbound(loc,s)       -> error ("Unbound: "^s^" at "^string_of_int loc.Location.loc_start.Lexing.pos_lnum)
    | e                    -> error (Printexc.to_string e)
  end;
  if not !quit then interact ()
