open Format

type cmp = Less | Leq

type call = int * int * cmp array * int array

type calls = call list

let debug_sct = ref false

let compose_arg a1 a2 =
  Array.map (fun i -> a2.(i)) a1

let compose_cmp c1 a1 c2 =
    Array.mapi (fun i c ->
      match c, c2.(a1.(i)) with
      | Less, _ | _, Less -> Less
      | _ -> Leq) c1

let compose c1 a1 c2 a2 =
  (compose_cmp c1 a1 c2, compose_arg a1 a2)

let max c1 c2 =
  let changed = ref false in
  let c = Array.mapi (fun i c1 ->
    match c1, c2.(i) with
    | Less, Leq -> changed := true; Leq
    | Leq, _    -> Leq
    | Less, _   -> Less) c1
  in
  !changed, c

let print_cmp ff c =
  match c with
  | Less -> fprintf ff "<"
  | Leq  -> fprintf ff "="

let print_call ff (i,j,c,a) =
  fprintf ff "%d <- %d(" i j;
  Array.iteri (fun i c -> fprintf ff "%a%d," print_cmp c a.(i)) c;
  fprintf ff ")%!"

let print_calls ff (l:calls) =
  List.iter (print_call ff) l

let decr c a =
  try
    Array.iteri (fun i c ->
    match c with
    | Less when a.(i) = i -> raise Exit
    | _ -> ()) c;
    false
  with
    Exit -> true

let sct ls =
  if !debug_sct then eprintf "sct start ... %!";
  let tbl = Hashtbl.create 31 in
  let count = ref 0 in
  let add_edge i j c a =
    let old = try Hashtbl.find tbl i with Not_found ->
      let t = Hashtbl.create 7 in
      Hashtbl.add tbl i t; t
    in
    try
      let c' = Hashtbl.find old (j,a) in
      let changed, c'' = max c' c in
      Hashtbl.replace old (j, a) c'';
      changed
    with Not_found ->
      Hashtbl.add old (j, a) c;
      true
  in
  List.iter (fun (i,j,c,a) ->
    if !debug_sct then eprintf "init: %a\n%!" print_call (i,j,c,a);
    ignore (add_edge i j c a)) ls;
  let new_edges = ref
    (Hashtbl.fold (fun i t acc ->
      Hashtbl.fold (fun (j,a) c acc -> (i,j,c,a)::acc) t acc) tbl [])
  in
  try
    while !new_edges <> [] do
      if !debug_sct then eprintf "start completion\n%!";
      let l = !new_edges in
      new_edges := [];
      List.iter (fun (i,j,c,a) ->
	try
	  let t' = Hashtbl.find tbl j in
	  Hashtbl.iter (fun (k, a') c' ->
	    let (c'',a'') = compose c a c' a' in
	    if !debug_sct then
	      eprintf "compose: %a %a -> %a "
		print_call (i,j,c,a)
		print_call (j,k,c',a')
		print_call (i,k,c'',a'');
	    if i = k && compose c'' a'' c'' a'' = (c'',a'') && not (decr c'' a'') then raise Exit;
	    if add_edge i k c'' a'' then (
	      if !debug_sct then eprintf "(new)\n%!";
	      incr count;
	      new_edges := (i,k,c'',a'') :: !new_edges)
	    else
	      if !debug_sct then eprintf "(old)\n%!";
	  ) t'
	  with Not_found -> ()) l
    done;
    eprintf "sct passed (%5d edges)\t%!" !count;
    true
  with Exit ->
    eprintf "sct failed (%5d edges)\t%!" !count;
    false
