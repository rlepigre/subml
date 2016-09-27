
type ('a, 'b) refinter =
  ('a * 'b) list option ref * 'a list * bool ref

let create l = (ref None, List.map fst l, ref false)

let subset : ('a -> 'a -> bool) -> ('a, 'b) refinter -> ('a * 'b) list -> bool =
  fun eq (set, forbidden, frozen) l ->
    if !frozen then
      match !set with
      | None -> true
      | Some set -> List.for_all (fun (x,_) -> List.exists (fun (y, _) -> eq x y) l) set
    else
      match !set with
      | None -> set := Some (List.filter (fun (x,_) ->
                            not (List.exists (fun y -> eq x y) forbidden)) l); true
      | Some l' ->
         set := Some (List.filter (fun (x,_) -> List.exists (fun (y, _) -> eq x y) l) l');
         true

let is_empty :  ('a, 'b) refinter -> bool =
  fun (set, forbidden, frozen) -> match !set with
  | Some [] -> true
  | _ -> false

let get : ('a, 'b) refinter -> ('a * 'b) list =
  fun (set, forbidden, frozen) ->
    frozen := true;
    match !set with
    | None -> set := Some []; []
    | Some l -> l
