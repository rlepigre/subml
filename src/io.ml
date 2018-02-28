(**{3 Output functions, general and for debugging channels}*)

open Format

type fmts =
  { mutable out : formatter
  ; mutable err : formatter
  ; mutable log : formatter
  ; mutable tex : formatter
  ; mutable gml : formatter }

let fmts =
  { out = std_formatter
  ; err = err_formatter
  ; log = err_formatter
  ; tex = std_formatter
  ; gml = std_formatter }

let out ff = fprintf  fmts.out ff
let err ff = fprintf  fmts.err ff
let log ff = fprintf  fmts.log ff
let tex ff = fprintf  fmts.tex ff
let nul ff = ifprintf fmts.log ff

let path : string list ref = ref Config.default_path

let read_file : (string -> Input.buffer) ref =
  let read_file fn =
    let add_fn dir = Filename.concat dir fn in
    let fs = fn :: (List.map add_fn !path) in
    let rec find = function
      | []     -> err "File %S not found.\n%!" fn; exit 1
      | fn::fs -> if Sys.file_exists fn then Input.from_file fn
                  else find fs
    in find fs
  in ref read_file

let file fn = !read_file fn

let ((fmt_of_file : string -> formatter), (close_files : unit -> unit)) =
  let channels = ref [] in
  let fmt_of_file fn =
    let ch = open_out fn in
    channels := ch :: !channels;
    formatter_of_out_channel ch
  in
  let close_files () =
    List.iter close_out !channels;
    channels := []
  in
  (fmt_of_file, close_files)

let set_tex_file : string -> unit =
  fun fn -> fmts.tex <- fmt_of_file fn
let set_gml_file : string -> unit =
  fun fn -> fmts.gml <- fmt_of_file fn

let debug = ref ""
let debug_sct = 'y'
let debug_uni = 'u'
let debug_sub = 's'
let debug_typ = 't'
let debug_mat = 'm'
let debug_ord = 'o'
let debug_ind = 'i'
let debug_all = "iyustmo"

let log_sct ff = if String.contains !debug debug_sct then log ff else nul ff
let log_uni ff = if String.contains !debug debug_uni then log ff else nul ff
let log_sub ff = if String.contains !debug debug_sub then log ff else nul ff
let log_typ ff = if String.contains !debug debug_typ then log ff else nul ff
let log_mat ff = if String.contains !debug debug_mat then log ff else nul ff
let log_ord ff = if String.contains !debug debug_ord then log ff else nul ff
let log_ind ff = if String.contains !debug debug_ind then log ff else nul ff

let set_debug s =
  debug := if s = "all" then debug_all else s
