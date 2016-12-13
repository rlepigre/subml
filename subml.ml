(****************************************************************************)
(**{3                                 Main file                            }*)
(****************************************************************************)
let quit    = ref false
let prelude = ref true
let files   = ref []

let spec = Arg.align
  [ ( "--verbose"
    , Arg.Set Ast.verbose
    , "  Display the defined types and values" )
  ; ( "--quit"
    , Arg.Set quit
    , "  Quit after evaluating the files" )
  ; ( "--no-prelude"
    , Arg.Clear prelude
    , "  Do not load the prelude" )
  ; ( "--htm-file"
    , Arg.String Io.(fun s -> fmts.htm <- fmt_of_file s)
    , "fn  Choose the TeX output file" )
  ; ( "--tex-file"
    , Arg.String Io.(fun s -> fmts.tex <- fmt_of_file s)
    , "fn  Choose the TeX output file" )
  ; ( "--out-file"
    , Arg.String Io.(fun s -> fmts.out <- fmt_of_file s)
    , "fn  Choose the standard output file" )
  ; ( "--err-file"
    , Arg.String Io.(fun s -> fmts.err <- fmt_of_file s)
    , "fn  Choose the error output file" )
  ; ( "--log-file"
    , Arg.String Io.(fun s -> fmts.log <- fmt_of_file s)
    , "fn  Choose the log output file" )
  ; ( "--no-inline"
    , Arg.Clear Sct.do_inline
    , "  Do not optimize the SCP call graph by inlining" )
  ; ( "--no-contr"
    , Arg.Clear Ast.contract_mu
    , "  Do not contract the fixpoints" )
  ; ( "--fix-depth"
    , Arg.Set_int Typing.fixpoint_depth
    , "i  Set the maximal unrolling depth for fixpoints" )
  ; ( "--debug"
    , Arg.String Io.set_debug
    , "s  Display the debugging informations
                   't': typing
                   's': subtyping
                   'u': unification
                   'y': size change principle
                   'm': sct matrix coefficient" )
  ; ( "-I"
    , Arg.String (fun s -> Config.path := s :: ! Config.path)
    , "s  Add the given directory to the path")
  ]

let _ =
  Sys.catch_break true;

  (* Reading the command lien arguments and gathering the files. *)
  let usage = Printf.sprintf "Usage: %s [ARGS] [FILES]" Sys.argv.(0) in
  Arg.parse spec (fun fn -> files := !files @ [fn]) usage;
  let files = if !prelude then "prelude.typ" :: !files else !files in

  (* Handle the files given on the command line. *)
  let eval = Parser.handle_exception Parser.eval_file in
  let ok = List.for_all eval files in

  (* Run the toplevel. *)
  let handle_line () = Parser.toplevel_of_string (read_line ()) in
  if not !quit && ok then
    begin try while true do
      Printf.printf ">> %!";
      ignore (Parser.handle_exception handle_line ())
    done with End_of_file -> () end;

  (* Close opened file and exit. *)
  Io.close_files ();
  if not ok then exit 1
