
type ('a, 'b) refinter =
  ('a * 'b) list option ref * bool ref

let create () = (ref None, ref false)

let subset : ('a -> 'a -> bool) -> ('a, 'b) refinter -> ('a * 'b) list -> bool =
  fun eq (set, frozen) l ->
    if !frozen then
      match !set with
      | None -> true
      | Some set -> List.for_all (fun (x,_) -> List.exists (fun (y, _) -> eq x y) l) set
    else
      match !set with
      | None -> set := Some l; true
      | Some l' ->
         set := Some (List.filter (fun (x,_) -> List.exists (fun (y, _) -> eq x y) l) l');
         true


let get : ('a, 'b) refinter -> ('a * 'b) list =
  fun (set, frozen) ->
    frozen := true;
    match !set with
    | None -> []
    | Some l -> l
