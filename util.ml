module IntOrd =
  struct
    type t = int
    let compare = compare
  end

module StringOrd =
  struct
    type t = string
    let compare = compare
  end

module IntSet = Set.Make (IntOrd)
module IntMap = Map.Make (IntOrd)

module StringMap = Map.Make (StringOrd)
module StringSet = Set.Make (StringOrd)

(* Type constructor to give position information in a source file. *)
type pos = Location.t

type 'a position =
  { elt : 'a
  ; pos : pos }

let in_pos : pos -> 'a -> 'a position = fun p e -> { elt = e; pos = p }

let dummy_position : pos = Location.none

let dummy_pos : 'a -> 'a position = fun e -> in_pos dummy_position e

(* Split an indentifier into a name and an integer. *)
let split s =
  let l = String.length s in
  let last_num = ref l in
  while !last_num > 0 && s.[!last_num-1] >= '0' && s.[!last_num-1] <= '9' do
    decr last_num
  done;
  let name = String.sub s 0 !last_num in
  let num = String.sub s !last_num (l - !last_num) in
  if name = "" then raise (Invalid_argument "split");
  (name, if num = "" then 0 else int_of_string num)
