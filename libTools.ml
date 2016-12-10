(****************************************************************************)
(**{3                         General functions                            }*)
(****************************************************************************)

(*{2 functions related to ['a option] }*)
let map_opt : ('a -> 'b) -> 'a option -> 'b option = fun f o ->
  match o with None -> None | Some e -> Some (f e)

let iter_opt : ('a -> unit) -> 'a option -> unit = fun f o ->
  match o with None -> () | Some e -> f e

let from_opt : 'a option -> 'a -> 'a = fun o d ->
  match o with None -> d | Some e -> e

let from_opt' : 'a option -> (unit -> 'a) -> 'a = fun o f ->
  match o with None -> f () | Some e -> e

(*{2 functions related to ['a list] }*)

let map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list = fun f l ->
  List.map (fun (k, v) -> (k, f v)) l

let assoc_gen : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b =
  fun eq o l ->
    let rec fn =
      function
      | [] -> raise Not_found
      | (o',v)::l -> if eq o o' then v else fn l
    in
    fn l

(*{2 functions related to [char] }*)

let int_of_chars : char list -> int = fun s ->
  let f acc c = acc * 10 + (Char.code c - Char.code '0') in
  List.fold_left f 0 (List.rev s)

let string_of_chars : char list -> string = fun s ->
  let s = Array.of_list s in
  let res = String.make (Array.length s) ' ' in
  Array.iteri (fun i c -> res.[i] <- c) s; res

(*{2 Miscelaneous }*)

(** clear the terminal *)
let clear : unit -> unit =
  fun () -> ignore (Sys.command "clear")
