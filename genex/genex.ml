let parser incl = "include \"" f:''[a-zA-Z0-9/._-]+'' "\"\n"

let parser sect =  "(*" name:''[A-Za-z0-9 -]*'' "*)\n" is:incl+ "\n" ->
  (String.trim name, is)

let parse = Decap.parse_file (parser sect*) Decap.no_blank

let output_html ss =
  let output_sect (n, is) =
    Printf.printf "<h3>%s</h3>\n" n;
    Printf.printf "<ul>\n";
    let print_link l =
      Printf.printf "  <li><a class=\"submlfile\" href=\"javascript:";
      Printf.printf "loadsubmlfile('%s')" l;
      Printf.printf "\">%s</a></li>\n" l
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
  output_html (Decap.handle_exception parse Sys.argv.(1)) 
