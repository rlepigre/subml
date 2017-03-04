let blank = Earley.blank_regexp "[ \n\r\t]*"

let parser incl = "include \"" f:''[a-zA-Z0-9/._-]+'' "\""

let parser sect =  "(*" name:''[A-Za-z0-9 -]*'' "*)" is:incl+ ->
  (String.trim name, is)

let parse = Earley.parse_file (parser sect*) blank

let eLink="enableJavascript.html"

let output_html ss =
  let print_link ch (n, l) =
    Printf.printf "<a class=\"submlfile\" href=\"%s\" title=\"load %s\" " eLink l;
    Printf.printf "onclick=\"loadsubmlfile('%s'); return false;\"" l;
    Printf.printf ">%s</a>\n" l
  in
  let output_sect (n, is) =
    match is with
    | []  -> ()
    | [l] -> Printf.printf "<h3>%s (%a)</h3>\n" l print_link (n, l);
    | _   -> Printf.printf "<h3>%s</h3>\n" n;
             Printf.printf "<ul>\n";
             let print_link l =
               Printf.printf "  <li>%a</li>\n" print_link (n, l)
             in
             List.iter print_link is;
             Printf.printf "</ul>\n"
  in
  List.iter output_sect ss

let _ =
  if Array.length Sys.argv <> 2 then
    begin
      Printf.eprintf "Usage: %s <all.typ>\n%!" Sys.argv.(0);
      exit 1;
    end;
  output_html (Earley.handle_exception parse Sys.argv.(1))
