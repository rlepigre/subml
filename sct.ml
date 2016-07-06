open Format

(* implementation of the sct we need for subtyping:
   all arguments of a call correpond to a parameter
   with a know relation : Less of Less of equal *)

type cmp = Less | Leq | Unknown

(* a call g(x0-1,x1,x1-1) inside f(x0,x1) is
   represented by (g_n, f_n, [|[| Less; Unknown; Unknown |];
                               [| Unknown; Leq; Less  |]|], b)

   more precisely, a call (i,j,m) represents a call
   to the function numbered i inside the function numbered j.
   m is a matrix. the coefficient m.(i).(j) give the relation
   between the i-th parameter of the caller and the j-th argument
   of the called function.

   The boolean in pre_call indicates a recursive call, that must no be
   removed by inlining.  *)
type call = int * int * cmp array array
type pre_call = int * int * cmp array array * bool

let compose c1 c2 = match c1, c2 with
  | Unknown, _ | _, Unknown -> Unknown
  | Less, _ | _, Less -> Less
  | Leq, Leq -> Leq

type calls = call list
type pre_calls = pre_call list
type arities = (int * (string * int)) list
type calls_graph = arities * calls

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
    let (_, a) = try List.assoc i tbl with Not_found -> assert false in
    for i = 0 to a - 1 do
      fprintf ff "%sX%d" (if i = 0 then "" else ",") i
    done
  in
  let (namei, _) = try List.assoc i tbl with Not_found -> assert false in
  let (namej, _) = try List.assoc j tbl with Not_found -> assert false in
  fprintf ff "%s%d(%a) <- %s%d(" namej j print_args j namei i;
  Array.iteri (fun i l ->
    if i > 0 then fprintf ff ",";
    let some = ref false in
    Array.iteri (fun j c ->
      if c <> Unknown then (
	let sep = if !some then " " else "" in
	fprintf ff "%s%aX%d" sep print_cmp c j;
	some := true
      )) l;
      if not !some then fprintf ff "?") m;
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
let (new_function : string -> int -> int), reset_function, pr_call, arities, arity =
  let count = ref 0 in
  let fun_table = ref [] in (* the table is only used for debugging messages *)
  (fun name arity ->
    let n = !count in
    incr count;
    fun_table := (n, (name, arity))::!fun_table;
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
let sct: calls -> bool = fun ls ->
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
    let (_, a) = List.assoc i arities in
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
	    let (_, a) = List.assoc k arities in
	    let (_, b) = List.assoc j arities in
	    let (_, c) = List.assoc i arities in
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


type count = Zero | One of call | More

let add_call n call = match n with
  | Zero -> One call
  | _ -> More

let do_inline = ref true

(* inline function that call only one function.
   TODO: inline function that are called at most once *)
let inline calls =
  if not !do_inline then
    List.map (fun (i,j,m,_) -> (i,j,m)) calls
  else
  (* eprintf "before inlining\n";
     List.iter (eprintf "%a\n%!" pr_call) calls; *)
  let tbl = Hashtbl.create 31 in
  List.iter (
    fun (i,j,m,rec_call) ->
      let old = try Hashtbl.find tbl i with Not_found -> Zero in
      let n = if rec_call then More else add_call old (i,j,m) in
      Hashtbl.replace tbl i n) calls;
  let rec fn (j,i,m,r) =
    try
      match Hashtbl.find tbl i with
      | One (_,k,m') ->
	 let (_, a) = arity k in
	 let (_, b) = arity i in
	 let (_, c) = arity j in
	 let call = (j,k,mat_prod a b c m' m,r) in
	 fn call
      | _ -> (j,i,m)
    with Not_found -> (j,i,m)
  in
  let calls =
    List.filter (fun (i,_,_,_) -> Hashtbl.find tbl i = More) calls
  in
  let calls = List.map fn calls in
  (* eprintf "after inlining\n";
     List.iter (eprintf "%a\n%!" pr_call) calls;*)
  calls
