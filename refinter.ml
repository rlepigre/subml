
type 'a refinter =
  'a list option ref * bool ref

let create () = (ref None, ref false)

let subset : ('a -> 'a -> bool) -> 'a refinter -> 'a list -> bool =
  fun eq (set, frozen) l ->
    if !frozen then
      match !set with
      | None -> true
      | Some set -> List.for_all (fun x -> List.exists (eq x) l) set
    else
      match !set with
      | None -> set := Some l; true
      | Some l' ->
	 set := Some (List.filter (fun x -> List.exists (eq x) l) l');
	 true


let get : 'a refinter -> 'a list =
  fun (set, frozen) ->
    frozen := true;
    match !set with
    | None -> []
    | Some l -> l
