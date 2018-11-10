(****************************************************************************)
(**{3                                 Main file                            }*)
(****************************************************************************)
let quit    = ref false

let spec = Arg.align
  [ ( "--verbose"
    , Arg.Set Ast.verbose
    , " Display the defined types and values" )
  ; ( "--quit"
    , Arg.Set quit
    , " Quit after evaluating the files" )
  ; ( "--gml-file"
    , Arg.String Io.set_gml_file
    , "fn Choose the GraphMl output file" )
  ; ( "--tex-file"
    , Arg.String Io.set_tex_file
    , "fn Choose the TeX output file" )
  ; ( "--out-file"
    , Arg.String Io.(fun s -> fmts.out <- fmt_of_file s)
    , "fn Choose the standard output file" )
  ; ( "--err-file"
    , Arg.String Io.(fun s -> fmts.err <- fmt_of_file s)
    , "fn Choose the error output file" )
  ; ( "--log-file"
    , Arg.String Io.(fun s -> fmts.log <- fmt_of_file s)
    , "fn Choose the log output file" )
  ; ( "--no-inline"
    , Arg.Clear Sct.do_inline
    , " Do not optimize the SCP call graph by inlining" )
  ; ( "--no-contr"
    , Arg.Clear Ast.contract_mu
    , " Do not contract the fixpoints" )
  ; ( "--fix-depth"
    , Arg.Set_int Raw.fixpoint_depth
    , "i Set the maximal unrolling depth for fixpoints" )
  ; ( "--debug"
    , Arg.String Io.set_debug
    , "s Display the debugging informations
                     't': typing
                     's': subtyping
                     'u': unification
                     'y': size change principle
                     'm': sct matrix coefficient" )
  ; ( "--debug-parser"
    , Arg.Set_int Earley_core.Earley.debug_lvl
    , "i Set the debug lvl of earley" )
  ; ( "-I"
    , Arg.String (fun s -> Io.path := s :: !Io.path)
    , "s Add the given directory to the path")
  ]

let _ =
  Sys.catch_break true;

  (* Reading the command lien arguments and gathering the files. *)
  let usage = Printf.sprintf "Usage: %s [ARGS] [FILES]" Sys.argv.(0) in
  let files =
    let files = ref [] in
    Arg.parse spec (fun fn -> files := !files @ [fn]) usage;
    !files
  in

  (* Handle the files given on the command line. *)
  let eval = Parser.handle_exception Parser.eval_file in
  let ok = List.for_all eval files in

  (* Run the toplevel. *)
  let handle_line () =
    let line = read_line () in
    if String.trim line <> "" then Parser.(execute (toplevel_of_string line))
  in
  if not !quit && ok then
    begin
      Ast.verbose := true;
      try while true do
        Printf.printf ">> %!";
        ignore (Parser.handle_exception handle_line ())
      done with End_of_file -> ()
    end;

  (* Close opened file and exit. *)
  Io.close_files ();
  if not ok then exit 1
