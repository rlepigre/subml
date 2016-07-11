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

let open_out, close_out =
  let tbl = Hashtbl.create 31 in
  (fun fn ->
    try let (ch,n) = Hashtbl.find tbl fn in
        Hashtbl.replace tbl fn (ch,n+1);
        ch
    with Not_found ->
      let ch = open_out fn in
      Hashtbl.add tbl fn (ch, 1);
      ch),
  (fun fn ->
    try let (ch,n) = Hashtbl.find tbl fn in
        if n = 1 then (
          close_out ch;
          Hashtbl.remove tbl fn)
        else
          Hashtbl.replace tbl fn (ch,n-1)
    with Not_found -> ()) (* FIXME: error ? *)

let file fn = Input.buffer_from_channel ~filename:fn (open_in fn)

let fmt_of_file fn = formatter_of_out_channel (open_out fn)

(*FIXME: close file, just need remembering the file *)
