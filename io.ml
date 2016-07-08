open Format

type io =
  { mutable stdout_fmt : formatter
  ; mutable stderr_fmt : formatter
  ; mutable log_fmt    : formatter
  ; mutable latex_fmt  : formatter
  }

let io =
  { stdout_fmt = std_formatter
  ; stderr_fmt = err_formatter
  ; log_fmt    = err_formatter
  ; latex_fmt  = std_formatter
  }

let out   ff = fprintf io.stdout_fmt ff
let err   ff = fprintf io.stderr_fmt ff
let log   ff = fprintf io.log_fmt    ff
let latex ff = fprintf io.latex_fmt  ff

let file fn = Input.buffer_from_channel ~filename:fn (open_in fn)

let fmt_of_file fn = formatter_of_out_channel (open_out fn)
