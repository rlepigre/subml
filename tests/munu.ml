(* Generator for examples with mixed induction and co-induction. *)
let size =
  try int_of_string Sys.argv.(1)
  with _ ->
    Printf.eprintf "Usage: %s <n>\n%!" Sys.argv.(0);
    exit 1

let lowercase = Array.init 26 (fun i -> Char.chr (Char.code 'a' + i))
let uppercase = Array.init 26 (fun i -> Char.chr (Char.code 'A' + i))

let type_constr name size =
  let aux i = Printf.sprintf "C%i of %c" (i+1) uppercase.(i) in
  let cstrs = Array.init size aux in
  let cstrs = String.concat " | " (Array.to_list cstrs) in
  let cstrs = "[C0 | " ^ cstrs ^ "]" in
  let aux i = Printf.sprintf "%c" uppercase.(i) in
  let args  = Array.init size aux in
  let args  = String.concat ", " (Array.to_list args) in
  let name  = name ^ "(" ^ args ^ ")" in
  (name, cstrs)

let rec permutations : 'a list -> 'a list list = function
  | []  -> []
  | [x]   -> [[x]]
  | l   ->
      let aux x =
        let lmx = List.filter (fun y -> y <> x) l in
        List.map (fun l -> x::l) (permutations lmx)
      in
      List.concat (List.map aux l)

let rec choice : 'a list -> ('a * bool) list list = function
  | []    -> []
  | [x]   -> [[(x,true)]; [(x,false)]]
  | x::xs -> let l = choice xs in
             let lxtru = List.map (fun l -> (x,true)::l) l in
             let lxfls = List.map (fun l -> (x,false)::l) l in
             lxtru @ lxfls

let permutations = permutations (Array.to_list (Array.init size (fun i -> i)))
let permutations = List.concat (List.map choice permutations)

let left_perm = choice (Array.to_list (Array.init size (fun i -> i)))

let test_permutations p1 p2 =
  let aux (i, is_mu1) =
    let is_mu2 = List.assoc i p2 in
    is_mu1 || not is_mu2
  in
  List.for_all aux p1 &&
  let aux = function
    | (i, true ) -> true
    | (i, false) ->
        let rec right_mu_of i = function
          | []   -> []
          | j::r when fst j = i -> List.map fst (List.filter (fun (_,b) -> b) r)
          | j::r -> right_mu_of i r
        in
        let left_mu_of i p =
          let rec left_mu acc = function
            | []   -> assert false
            | j::r when fst j = i -> List.rev_map fst acc
            | j::r -> left_mu (if snd j then j::acc else acc) r
          in left_mu [] p
        in
        let right_mu = right_mu_of i p1 in
        let left_mu = left_mu_of i p2 in
        List.for_all (fun e -> not (List.mem e left_mu)) right_mu
  in
  List.for_all aux p1

let _ =
  let (args, cstrs) = type_constr "T" size in
  Printf.printf "(* Type constructor definition. *)\n%!";
  Printf.printf "type %s = %s\n\n" args cstrs;

  Printf.printf "(* Type definitions. *)\n%!";
  let print_type p =
    Printf.printf "type T";
    let aux = function
      | (i, true ) -> Printf.printf "%c" lowercase.(i)
      | (i, false) -> Printf.printf "%c" uppercase.(i)
    in
    List.iter aux p;
    Printf.printf " = ";
    let aux = function
      | (i, true ) -> Printf.printf "μ%c." uppercase.(i)
      | (i, false) -> Printf.printf "ν%c." uppercase.(i)
    in
    List.iter aux p;
    Printf.printf "%s\n%!" cstrs
  in
  List.iter print_type permutations;

  Printf.printf "\n(* The tests. *)\n%!";
  List.iter (fun p1 -> List.iter (fun p2 ->
    let aux = function
      | (i, true ) -> Printf.printf "%c" lowercase.(i)
      | (i, false) -> Printf.printf "%c" uppercase.(i)
    in
    let no = if test_permutations p1 p2 then "" else "!" in
    Printf.printf "%scheck T" no;
    List.iter aux p1;
    Printf.printf " ⊂ T";
    List.iter aux p2;
    Printf.printf "\n%!"
  ) permutations) left_perm
