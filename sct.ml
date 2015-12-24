open Format

(* implementation of the sct we need for subtyping:
   all arguments of a call correpond to a parameter
   with a know relation : Less of Less of equal *)

type cmp = Less | Leq

(* a call g(x0-1,x1,x1-1) inside f(x0,x1) is
   represented by (g_n, f_n, [|Less;Leq;Less|] [|0;1;1|])

   more precisely, a call (i,j,c,a) represents a call
   to the function numbered i inside the function numbered j.
   a indicates which parameters of j are used in the call.
   c indicates the relation with this parameter *)
type call = int * int * cmp array * int array

type calls = call list

let debug_sct = ref false

(* call composition *)
let compose_arg a1 a2 =
  Array.map (fun i -> a2.(i)) a1

let compose_cmp c1 a1 c2 =
    Array.mapi (fun i c ->
      match c, c2.(a1.(i)) with
      | Less, _ | _, Less -> Less
      | _ -> Leq) c1

let compose c1 a1 c2 a2 =
  (compose_cmp c1 a1 c2, compose_arg a1 a2)

(* maximum of two call relation for subsumption
   max c1 c2 returns true if it returns c1  *)
let max c1 c2 =
  let changed = ref false in
  let c = Array.mapi (fun i c1 ->
    match c1, c2.(i) with
    | Less, Leq -> changed := true; Leq
    | Leq, _    -> Leq
    | Less, _   -> Less) c1
  in
  !changed, c

(* printing function for debugging *)
let print_cmp ff c =
  match c with
  | Less -> fprintf ff "<"
  | Leq  -> fprintf ff "="

let print_call tbl ff (i,j,c,a) =
  let print_args ff i =
    let a = try List.assoc i tbl with Not_found -> assert false in
    for i = 0 to a - 1 do
      fprintf ff "%sX%d" (if i = 0 then "" else ",") i
    done
  in
  fprintf ff "F%d(%a) <- F%d(" j print_args j i;
  Array.iteri (fun i c ->
    fprintf ff "%s%aX%d" (if i = 0 then "" else ",") print_cmp c a.(i)) c;
  fprintf ff ")%!"

let print_calls tbl ff (l:calls) =
  List.iter (print_call tbl ff) l

(* check is a call (supposed idempotnent) is
   decreasing *)
let decr c a =
  try
    Array.iteri (fun i c ->
    match c with
    | Less when a.(i) = i -> raise Exit
    | _ -> ()) c;
    false
  with
    Exit -> true

(* function needs to be declared. calling sct will
   reset the function table *)
let (new_function : int -> int), reset_function =
  let count = ref 0 in
  let fun_table = ref [] in (* the table is only used for debugging messages *)
  (fun arity ->
    let n = !count in
    incr count;
    fun_table := (n, arity)::!fun_table;
    n),
  (fun () ->
    let res = (!count, !fun_table) in
    count := 0;
    fun_table := [];
    res)

module IntArray = struct
  type t = int array
  let compare = compare
end

module IAMap = Map.Make(IntArray)

(* the main function *)
let sct: ?summary:bool -> call list -> bool = fun ?(summary=false) ls ->
  if !debug_sct then eprintf "sct start ... %!";
  let num_fun, arities = reset_function () in
  let tbl = Array.init num_fun (fun _ -> Array.make num_fun IAMap.empty) in
  let print_call = print_call arities in
  (* counters to count added and tested edges *)
  let added = ref 0 and tested = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j c a =
    (* test idempotent edges as soon as they are discovered *)
    if i = j && compose c a c a = (c,a) && not (decr c a) then raise Exit;
    let ti = tbl.(i) in
    try
      let c' = IAMap.find a ti.(j) in
      let changed, c'' = max c' c in
      ti.(j) <- IAMap.add a c'' ti.(j);
      changed
    with Not_found ->
      ti.(j) <- IAMap.add a c ti.(j);
      true
  in
  (* adding initial edges *)
  try
    List.iter (fun (i,j,c,a) ->
      if !debug_sct then eprintf "\tinit: %a\n%!" print_call (i,j,c,a);
      ignore (add_edge i j c a)) ls;
    (* collecting all edges (there may be less that initially
       because of subsumption *)
    let new_edges = ref [] in
    Array.iteri (fun i t ->
      Array.iteri (fun j t ->
	IAMap.iter (fun a c ->
	  new_edges := (i,j,c,a)::!new_edges) t) t) tbl;
    (* compute the transitive closure of the call graph *)
    if !debug_sct then eprintf "start completion\n%!";
    let rec fn () =
      match !new_edges with
	[] -> ()
      | (i,j,c,a)::l ->
	 new_edges := l;
	let t' = tbl.(j) in
	Array.iteri (fun k t -> IAMap.iter (fun a' c' ->
	  let (c'',a'') = compose c a c' a' in
	  incr tested;
	  if !debug_sct then
	    eprintf "\tcompose: %a * %a = %a "
	      print_call (i,j,c,a)
	      print_call (j,k,c',a')
	      print_call (i,k,c'',a'');
	  if add_edge i k c'' a'' then (
	    if !debug_sct then eprintf "(new)\n%!";
	    incr added;
	    new_edges := (i,k,c'',a'') :: !new_edges)
	  else
	    if !debug_sct then eprintf "(old)\n%!";
	) t) t';
	fn ()
    in
    fn ();
    if !debug_sct || summary then
      eprintf "sct passed (%5d edges added, %6d tested)\t%!" !added !tested;
    true
  with Exit ->
    if !debug_sct then eprintf "looping idempotent call!\n%!";
    if !debug_sct || summary then
      eprintf "sct failed (%5d edges added, %6d tested)\t%!" !added !tested;
    false
