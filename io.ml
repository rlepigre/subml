open Format

type fmts =
  { mutable out : formatter
  ; mutable err : formatter
  ; mutable log : formatter
  ; mutable tex : formatter }

let fmts =
  { out = std_formatter
  ; err = err_formatter
  ; log = err_formatter
  ; tex = std_formatter }

let out ff = fprintf fmts.out ff
let err ff = fprintf fmts.err ff
let log ff = fprintf fmts.log ff
let tex ff = fprintf fmts.tex ff

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

let file fn = Input.buffer_from_channel ~filename:fn (open_in fn)

let fmt_of_file fn = formatter_of_out_channel (open_out fn)

(*FIXME: close file, just need remembering the file *)
