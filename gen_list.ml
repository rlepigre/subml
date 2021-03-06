(** Generate HTML menu for the SubML library using "lib/all.typ". *)

let is_empty : string -> bool = fun str ->
  String.trim str = ""

let is_title : string -> bool = fun str ->
  let str = String.trim str in
  let len = String.length str in
  if len < 6 then false else
  str.[0] = '(' && str.[1] = '*' && str.[2] = '*' && str.[len-2] = '*'
  && str.[len-1] = ')'

let get_title : string -> string = fun str ->
  let str = String.trim str in
  let len = String.length str in
  String.trim (String.sub str 3 (len - 5))

let is_comment : string -> bool = fun str ->
  let str = String.trim str in
  let len = String.length str in
  if len < 5 then false else
  str.[0] = '(' && str.[1] = '*' && str.[len-2] = '*' && str.[len-1] = ')'

let get_comment : string -> string = fun str ->
  let str = String.trim str in
  let len = String.length str in
  String.trim (String.sub str 2 (len - 4))

let is_include : string -> bool = fun str ->
  let str = String.trim str in
  let len = String.length str in
  len > 15 && String.sub str 0 9 = "include \"" && str.[len-1] = '"'

let get_include : string -> string = fun str ->
  let str = String.trim str in
  let len = String.length str in
  String.sub str 9 (len - 10)

type info = string option * string

let parse : string -> (string * info list) list = fun file ->
  let ic = open_in file in
  let data = ref [] in
  try while true do
    let line = input_line ic in
    if not (is_empty line) then
      begin
        if is_title   line then data := `Tit(get_title   line) :: !data else
        if is_comment line then data := `Com(get_comment line) :: !data else
        if is_include line then data := `Inc(get_include line) :: !data else
        failwith (Printf.sprintf "invalid line %S" line)
      end
  done; assert false with End_of_file ->
  close_in ic;
  let rec build ok acc data =
    match data with
    | `Tit com :: data -> build ((com,acc)::ok) [] data
    | `Inc inc :: `Com com :: data -> build ok ((Some com,inc)::acc) data
    | `Inc inc :: data -> build ok ((None, inc)::acc) data
    | _                -> if acc <> [] then failwith "ill-formed file"; ok
  in
  build [] [] !data

let output_html (ss : (string * info list) list) =
  let eLink="enableJavascript.html" in
  let print_link ch (n, l) =
    Printf.fprintf ch "<a class=\"submlfile\" href=\"%s\" " eLink;
    Printf.fprintf ch "title=\"load %s\" " l;
    Printf.fprintf ch "onclick=\"loadsubmlfile('%s'); return false;\"" l;
    Printf.fprintf ch ">%s</a>" l
  in
  let print_desc ch d =
    match d with
    | None   -> ()
    | Some s -> Printf.fprintf ch ": %s " s
  in
  let output_sect (n, is) =
    match is with
    | []      -> ()
    | [(d,l)] ->
        Printf.printf "<h3>%s (%a)</h3>\n" n print_link (n, l);
    | _       ->
        Printf.printf "<h3>%s</h3>\n" n;
        Printf.printf "<ul>\n";
        let print_link (d,l) =
          Printf.printf "  <li>%a%a</li>\n" print_link (n, l) print_desc d
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
  try output_html (parse Sys.argv.(1)) with Failure(msg) ->
    Printf.eprintf "ERROR: %s\n%!" msg;
    exit 1
