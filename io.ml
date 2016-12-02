open Format

type fmts =
  { mutable out : formatter
  ; mutable err : formatter
  ; mutable log : formatter
  ; mutable tex : formatter
  ; mutable htm : formatter }

let fmts =
  { out = std_formatter
  ; err = err_formatter
  ; log = err_formatter
  ; tex = std_formatter
  ; htm = std_formatter }

let out ff = fprintf  fmts.out ff
let err ff = fprintf  fmts.err ff
let log ff = fprintf  fmts.log ff
let tex ff = fprintf  fmts.tex ff
let nul ff = ifprintf fmts.log ff

let read_file : (string -> Input.buffer) ref = ref (fun name ->
  let rec fn = function
    | [] -> err "Can not open file %S\n%!" name; exit 1
    | path::l ->
       try
         let filename = Filename.concat path name in
         let ch = open_in filename in
         Gc.finalise close_in ch;
         Input.from_channel ~filename (open_in filename)
       with _ -> fn l
  in
  fn (""::!Config.path))

let file fn = !read_file fn

let fmt_of_file fn = formatter_of_out_channel (open_out fn)

let debug = ref ""
let debug_sct = 'y'
let debug_uni = 'u'
let debug_sub = 's'
let debug_typ = 't'
let debug_mat = 'm'
let debug_ord = 'o'
let debug_all = "yustmo"

let log_sct ff = if String.contains !debug debug_sct then log ff else nul ff
let log_uni ff = if String.contains !debug debug_uni then log ff else nul ff
let log_sub ff = if String.contains !debug debug_sub then log ff else nul ff
let log_typ ff = if String.contains !debug debug_typ then log ff else nul ff
let log_mat ff = if String.contains !debug debug_mat then log ff else nul ff
let log_ord ff = if String.contains !debug debug_ord then log ff else nul ff

let set_debug s =
  debug := if s = "all" then debug_all else s

(*FIXME: close file, just need remembering the file *)
