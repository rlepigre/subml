open Format

(* implementation of the sct we need for subtyping:
   all arguments of a call correpond to a parameter
   with a know relation : Less of Less of equal *)

type cmp = Less | Leq | Unknown

(* a call g(x0-1,x1,x1-1) inside f(x0,x1) is
   represented by (g_n, f_n, [|Less;Leq;Less|] [|0;1;1|])

   more precisely, a call (i,j,c,a) represents a call
   to the function numbered i inside the function numbered j.
   a indicates which parameters of j are used in the call.
   c indicates the relation with this parameter *)
type call = int * int * cmp array array
  (* index of the caller for lines *)

let compose c1 c2 = match c1, c2 with
  | Unknown, _ | _, Unknown -> Unknown
  | Less, _ | _, Less -> Less
  | Leq, Leq -> Leq

type calls = call list

let debug_sct = ref false
let summary_sct = ref false

let mat_prod l1 c1 c2 m1 m2 =
  Array.init l1 (fun i ->
    Array.init c2 (fun j ->
      let r = ref Unknown in
      for k = 0 to c1 - 1 do
	r := min !r (compose m1.(i).(k) m2.(k).(j))
      done;
      !r
    ))

(* printing function for debugging *)
let print_cmp ff c =
  match c with
  | Unknown -> fprintf ff "?"
  | Less -> fprintf ff "<"
  | Leq  -> fprintf ff "="

let print_call tbl ff (i,j,m) =
  let print_args ff i =
    let a = try List.assoc i tbl with Not_found -> assert false in
    for i = 0 to a - 1 do
      fprintf ff "%sX%d" (if i = 0 then "" else ",") i
    done
  in
  fprintf ff "F%d(%a) <- F%d(" j print_args j i;
  Array.iteri (fun i l ->
    if i > 0 then fprintf ff ",";
    Array.iteri (fun j c ->
      (*      if c <> Unknown then*)
      fprintf ff "%aX%d " print_cmp c j) l) m;
  fprintf ff ")%!"

let print_calls tbl ff (l:calls) =
  List.iter (print_call tbl ff) l

(* check is a call (supposed idempotnent) is
   decreasing *)
let decrease m =
  try
    Array.iteri (fun i l ->
      match l.(i) with
      | Less -> raise Exit
      | _ -> ()) m;
    false
  with
    Exit -> true

module IntArray = struct
  type t = int array
  let compare = compare
end

module IAMap = Map.Make(IntArray)

(* function needs to be declared. calling sct will
   reset the function table *)
let (new_function : int -> int), reset_function, pr_call, arities, arity =
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
    res),
  (fun ch ->
    print_call !fun_table ch),
  (fun () -> !fun_table),
  (fun i -> try List.assoc i !fun_table with Not_found -> assert false)

let subsume m1 m2 =
  try
    Array.iteri (fun i l1 ->
      Array.iteri (fun j x ->
	if not (x >= m2.(i).(j)) then raise Exit) l1) m1;
    true
  with
    Exit -> false

(* the main function *)
let sct: call list -> bool = fun ls ->
  if !debug_sct then eprintf "SCT starts...\n%!";
  let num_fun, arities = reset_function () in
  let tbl = Array.init num_fun (fun _ -> Array.make num_fun []) in
  let print_call = print_call arities in
  (* counters to count added and composed edges *)
  let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j m =
    (* test idempotent edges as soon as they are discovered *)
    let a = List.assoc i arities in
    if i = j && mat_prod a a a m m = m && not (decrease m) then begin
      if !debug_sct then eprintf "edge %a idempotent and looping\n%!" print_call (i,j,m);
      raise Exit;
    end;
    let ti = tbl.(i) in
    let ms = ti.(j) in
    if List.exists (fun m' -> subsume m' m) ms then
      false
    else (
      let ms = m :: List.filter (fun m' -> not (subsume m m')) ms in
      ti.(j) <- ms;
      true)
  in
  (* adding initial edges *)
  try
    if !debug_sct then (
      eprintf "initial edges to be added:\n%!";
      List.iter (fun c -> eprintf "\t%a\n%!" print_call c) ls);
    let new_edges = ref ls in
    (* compute the transitive closure of the call graph *)
    if !debug_sct then eprintf "start completion\n%!";
    let rec fn () =
      match !new_edges with
	[] -> ()
      | (i,j,m)::l ->
	 new_edges := l;
	if add_edge i j m then begin
	  if !debug_sct then eprintf "\tedge %a added\n%!" print_call (i,j,m);
	  incr added;
	  let t' = tbl.(j) in
	  Array.iteri (fun k t -> List.iter (fun m' ->
	    if !debug_sct then
	      eprintf "\tcompose: %a * %a = %!"
		print_call (i,j,m)
		print_call (j,k,m');
	    let a = List.assoc k arities in
	    let b = List.assoc j arities in
	    let c = List.assoc i arities in
	    let m'' = mat_prod a b c m' m in
	    incr composed;
	    new_edges := (i,k,m'') :: !new_edges;
	    if !debug_sct then
	      eprintf "%a\n%!"
		print_call (i,k,m'');
	  ) t) t'
	end else
	  if !debug_sct then eprintf "\tedge %a is old\n%!" print_call (i,j,m);
	fn ()
    in
    fn ();
    if !debug_sct || !summary_sct then
      eprintf "SCT passed (%5d edges added, %6d composed)\t%!" !added !composed;
    true
  with Exit ->
    if !debug_sct || !summary_sct then
      eprintf "SCT failed (%5d edges added, %6d composed)\t%!" !added !composed;
    false
