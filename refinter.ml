
type 'a refinter = 'a list option ref * 'a list * bool ref

let create l = (ref None, l, ref false)

let subset : ('a -> 'a -> bool) -> 'a refinter -> 'a list -> bool =
  fun eq (set, forbidden, frozen) l ->
    if !frozen then
      match !set with
      | None -> true
      | Some set -> List.for_all (fun x -> List.exists (fun y -> eq x y) l) set
    else
      match !set with
      | None -> set := Some (List.filter (fun x ->
                            not (List.exists (fun y -> eq x y) forbidden)) l); true
      | Some l' ->
         set := Some (List.filter (fun x -> List.exists (fun y -> eq x y) l) l');
         true

let is_empty :  'a refinter -> bool =
  fun (set, forbidden, frozen) -> match !set with
  | Some [] -> true
  | _ -> false

let get : 'a refinter -> 'a list =
  fun (set, forbidden, frozen) ->
    frozen := true;
    match !set with
    | None -> set := Some []; []
    | Some l -> l
