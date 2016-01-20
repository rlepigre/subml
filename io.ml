open Format

type io = { mutable stdout : 'a. ('a, formatter, unit) format -> 'a;
	    mutable log    : 'a. ('a, formatter, unit) format -> 'a;
	    mutable stderr : 'a. ('a, formatter, unit) format -> 'a;
	    mutable files  : string -> Input.buffer
	  }

let io = {
  stdout = (fun format -> fprintf std_formatter format);
  log    = (fun format -> fprintf std_formatter format);
  stderr = (fun format -> fprintf err_formatter format);
  files  = (fun fname ->
    let ch = open_in fname in
    Input.buffer_from_channel ch);
}
