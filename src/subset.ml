(****************************************************************************)
(**{3       Implementattion of mutable sets via subset constraints         }*)
(****************************************************************************)

type 'a elts = Finite of 'a list | CoFinite of 'a list

type 'a set = { mutable set : 'a elts
                (** The current value of the set. *)
              ; mutable frozen : bool
                (** if true, the set is frozen and will not change anymore *) }

let create l = { set = CoFinite l; frozen = false }

(** test if a set is contained in a list for the given equality.
    if the set is not frozen, it will decrease *)
let test : ('a -> 'a -> bool) -> 'a set -> 'a list -> bool =
  fun eq set l ->
    if set.frozen then
      match set.set with
      | CoFinite _ -> assert false (* enforced by get *)
      | Finite l' -> List.for_all (fun x -> List.exists (fun y -> eq x y) l) l'
    else
      (* when the set is not fixed we change set into (set inter (Finite l))*)
      match set.set with
      | CoFinite l' -> set.set <- Finite (List.filter (fun x ->
                              not (List.exists (fun y -> eq x y) l')) l); true
      | Finite l' ->
         set.set <- Finite (List.filter (fun x -> List.exists (fun y -> eq x y) l) l');
         true

(** check if a set is empty *)
let is_empty :  'a set -> bool =
  fun set -> match set.set with
  | Finite [] -> true
  | _ -> false

(** get the current value of a set and froze it *)
let get : 'a set -> 'a list =
  fun set ->
    set.frozen <- true;
    match set.set with
    | CoFinite _ -> set.set <- Finite []; []
    | Finite l -> l

(** get the current value of a set without frozing it.
    should only be used for printing. Return [] for CoFinite *)
let unsafe_get : 'a set -> 'a list =
  fun set ->
    match set.set with
    | CoFinite _ -> []
    | Finite l -> l
