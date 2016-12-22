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
  let b = Buffer.create 10 in
  List.iter (Buffer.add_char b) s;
  Buffer.contents b

(*{2 Bindlib extension }*)

open Bindlib

type ('a,'b,'c) mmbinder = ('a, ('b,'c) mbinder) mbinder

let mmbinder_arities : type a b c.(a,b,c) mmbinder -> a -> int * int = fun b dum ->
  let aa = mbinder_arity b in
  let b = msubst b (Array.make aa dum) in
  let ba = mbinder_arity b in
  (aa, ba)

let mmbinder_names : type a b c.(a,b,c) mmbinder -> a -> string array * string array = fun b dum ->
  let aa = mbinder_arity b in
  let an = mbinder_names b in
  let b = msubst b (Array.make aa dum) in
  let bn = mbinder_names b in
  (an, bn)

let mmsubst b xs ys = msubst (msubst b xs) ys

let mmsubst_dummy b duma dumb =
  let (aa, bb) = mmbinder_arities b duma in
  mmsubst b (Array.make aa duma) (Array.make bb dumb)

(*{2 Miscelaneous }*)

(** clear the terminal *)
let clear : unit -> unit =
  fun () -> ignore (Sys.command "clear")
