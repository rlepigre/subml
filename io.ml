open Format

type fmts =
  { mutable out : formatter
  ; mutable err : formatter
  ; mutable log : formatter
  ; mutable tex : formatter
  ; mutable htm : formatter }

let read_file : (string -> Input.buffer) ref =
  let read_file filename =
    Input.buffer_from_channel ~filename (open_in filename)
  in ref read_file

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

let (open_out, close_out) =
  let tbl = Hashtbl.create 31 in
  let open_out fn =
    match Hashtbl.find tbl fn with
    | (ch, n)             -> Hashtbl.replace tbl fn (ch,n+1); ch
    | exception Not_found -> let ch = open_out fn in
                             Hashtbl.add tbl fn (ch,1); ch
  in
  let close_out fn =
    match Hashtbl.find tbl fn with
    | (ch,n)   when n = 1 -> close_out ch; Hashtbl.remove tbl fn
    | (ch,n)              -> Hashtbl.replace tbl fn (ch,n-1)
    | exception Not_found -> invalid_arg ("The file " ^ fn ^ " is not open.")
  in
  (open_out, close_out)

let file fn = !read_file fn

let fmt_of_file fn = formatter_of_out_channel (open_out fn)

let debug = ref ""
let debug_sct = 'y'
let debug_uni = 'u'
let debug_sub = 's'
let debug_typ = 't'
let debug_mat = 'm'
let debug_all = "musyt"

let log_sct ff = if String.contains !debug debug_sct then log ff else nul ff
let log_uni ff = if String.contains !debug debug_uni then log ff else nul ff
let log_sub ff = if String.contains !debug debug_sub then log ff else nul ff
let log_typ ff = if String.contains !debug debug_typ then log ff else nul ff
let log_mat ff = if String.contains !debug debug_mat then log ff else nul ff

let set_debug s =
  debug := if s = "all" then debug_all else s

(*FIXME: close file, just need remembering the file *)
