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
    , Arg.Clear Type.contract_mu
    , "  Do not contract the fixpoints" )
  ; ( "--fix-depth"
    , Arg.Set_int Typing.fixpoint_depth
    , "i  Set the maximal unrolling depth for fixpoints" )
  ; ( "--debug"
    , Arg.String Io.set_debug
    , "s  Display the debugging informations\n   't': typing\n   's': subtyping\n   'u': unification\n   'y': size change principle\n   'm': matrix coefficient" )
  ]

let usage = Printf.sprintf "Usage: %s [ARGS] [FILES]" Sys.argv.(0)

let rec interact () =
  Printf.printf ">> %!";
  let loop () = Parser.toplevel_of_string (read_line ()) in
  if Parser.handle_exception loop () then exit 0;
  interact ()

let _ =
  System.handle_stop true;
  Arg.parse spec (fun fn -> files := !files @ [fn]) usage;
  let files = if !prelude then "lib/prelude.typ" :: !files else !files in
  let eval = Parser.handle_exception Parser.eval_file in
  if not (List.for_all eval files) then exit 1;
  if not !quit then interact ()
