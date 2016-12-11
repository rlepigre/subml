(*****************************************************************************)
(**{3                 Size change termination principle                     }*)
(**         Chin Soon Lee, Neil D. Jones, Amir M. Ben-AmramPOPL2001          *)
(*****************************************************************************)
open Format

(** Implementation of the sct we need for subtyping and typing:

    - In the case of subtyping, all arguments of a call correpond to a
      parameter with a known relation : Less or Less or equal. In
      this case the sct is a decision procedure

    - For typing recursive program, general SCT is used and it is
      only a correct termination criteria *)

(*****************************************************************************)
(**{2                     General functions and types                       }*)
(*****************************************************************************)

type cmp =
  | Less (** argument is stricly smaller than the calling parameter *)
  | Leq  (** argument is less of equal than the calling parameter   *)
  | Unknown (** no relation is known between the argument and the parameter *)

(**a call g(x0-1,x1,x1-1) inside f(x0,x1) is
   represented by (g_n, f_n, [|[| Less; Unknown; Unknown |];
                               [| Unknown; Leq; Less  |]|], b)

   more precisely, a call (i,j,m) represents a call
   to the function numbered i inside the function numbered j.
   m is a matrix. the coefficient m.(a).(b) give the relation
   between the a-th parameter of the caller and the b-th argument
   of the called function.

   The boolean in call indicates a recursive call, that must not be
   removed by inlining. The boolean is true when the call is a recursive
    call. i.e. A call to a generalised hypothesis lower in the tree.
    More precisely, each subtyping in a typing, each rule introducing
    a new induction hypothesis has a false boolean. All other call
    are call to an induction hypothesis and have a true boolean.
*)
type index = int (** index of a function *)
type call = index * index * cmp array array * bool
type calls = call list


(** TODO: this is not very clean *)
type printer = (formatter -> unit) * (formatter -> unit) (* normal / latex *)

(** This stores the function table, giving name, arity and the
    way to print the function for debugging *)
type arities = (int * (string * int * printer array)) list
type call_table =
  { mutable current : int;
    mutable table : arities;
    mutable calls : calls
  }

(** Initialisation of a new function table *)
let init_table () =
  { current = 0
  ; table = [(-1, ("R", 0, [||]))] (* the root call is predefined *)
  ; calls = []
  }

(** the root index *)
let root = -1

(** Creation of a new function, return the function index in the table *)
let new_function : call_table -> string -> printer list -> index =
  fun ftbl name args ->
    let args = Array.of_list args in
    let arity = Array.length args in
    let n = ftbl.current in
    ftbl.current <- n + 1;
    ftbl.table <- (n, (name, arity, args))::ftbl.table;
    n

let new_call : call_table -> call -> unit = fun tbl call ->
  tbl.calls <- call::tbl.calls

(** Gives the arity of a given function *)
let arity : int -> call_table -> int = fun i ftbl ->
  try let (_,a,_) = List.assoc i ftbl.table in a
  with Not_found -> assert false

let copy t = { current = t.current; table = t.table; calls = t.calls }

let is_empty tbl = tbl.calls = []

(*****************************************************************************)
(**{2               Printing functions for debugging                        }*)
(*****************************************************************************)

let prInd ff = fprintf ff "%d"
let strInd = string_of_int
let prCmp ff c =
  match c with
  | Unknown -> fprintf ff "?"
  | Less -> fprintf ff "<"
  | Leq  -> fprintf ff "="
let strCmp c =
  match c with
  | Unknown -> "?"
  | Less -> "<"
  | Leq  -> "="

let print_call ff tbl (i,j,m,_) =
  let (_, aj, prj) = try List.assoc j tbl with Not_found -> assert false in
  let (_, ai, _) = try List.assoc i tbl with Not_found -> assert false in
  let print_args ff =
    for j = 0 to aj - 1 do
      fprintf ff "%s%t" (if j = 0 then "" else ",") (fst prj.(j))
    done
  in
  let (namei, _, _) = try List.assoc i tbl with Not_found -> assert false in
  let (namej, _, _) = try List.assoc j tbl with Not_found -> assert false in
  fprintf ff "%s%d(%t%!) <- %s%d%!(" namej j print_args namei i;
  for i = 0 to ai - 1 do
    if i > 0 then fprintf ff ",";
    let some = ref false in
    for j = 0 to aj - 1 do
      let c = m.(j).(i) in
      if c <> Unknown then (
      let sep = if !some then " " else "" in
      fprintf ff "%s%a%t" sep prCmp c (fst prj.(j));
      some := true)
    done
  done;
  fprintf ff ")%!"

let print_calls : formatter -> call_table -> unit = fun ff tbl ->
  List.iter (print_call ff tbl.table) tbl.calls

let latex_print_calls ff tbl =
  let arities = tbl.table in
  let calls = tbl.calls in
  let prCmp ff c =
    match c with
    | Unknown -> fprintf ff "?"
    | Less    -> fprintf ff "<"
    | Leq     -> fprintf ff "="
  in
  fprintf ff "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  let print_args ff j =
    let (_, aj, prj) =
      try List.assoc j arities with Not_found -> assert false
    in
    for j = 0 to aj - 1 do
      fprintf ff "%s%t" (if j = 0 then "" else ",") (snd prj.(j))
    done
  in
  let f (j,_) =
    fprintf ff "    N%d [ label = \"I_%d(%a)\" ];\n" j j print_args j
  in
  List.iter f (List.filter (fun (i,_) ->
    List.exists (fun (j,k,_,_) -> i = j || i =k) calls) arities);
  let print_call arities (i,j,m,_) =
    let (namej, aj, prj) =
      try List.assoc j arities with Not_found -> assert false
    in
    let (namei, ai, pri) =
      try List.assoc i arities with Not_found -> assert false
    in
    fprintf ff "    N%d -> N%d [label = \"(" j i;
    for i = 0 to ai - 1 do
      if i > 0 then fprintf ff ",";
      let some = ref false in
      for j = 0 to aj - 1 do
        let c = m.(j).(i) in
        if c <> Unknown then (
          let sep = if !some then " " else "" in
          fprintf ff "%s%a%t" sep prCmp c (snd prj.(j));
          some := true)
      done;
      if not !some then fprintf ff "?";
    done;
    fprintf ff ")\"]\n%!"
  in
  List.iter (print_call arities) calls;
  fprintf ff "  }\n\\end{dot2tex}\n"

(*****************************************************************************)
(**{2                   Basic operations on matrices                        }*)
(*****************************************************************************)

(** Composition of size change information *)
let compose c1 c2 = match c1, c2 with
  | Unknown, _ | _, Unknown -> Unknown
  | Less, _ | _, Less -> Less
  | Leq, Leq -> Leq

(** The induced matric product *)
let mat_prod l1 c1 c2 m1 m2 =
  Array.init l1 (fun i ->
    Array.init c2 (fun j ->
      let r = ref Unknown in
      for k = 0 to c1 - 1 do
        r := min !r (compose m1.(i).(k) m2.(k).(j))
      done;
      !r
    ))

(** Check if a call (supposed idempotnent) is decreasing *)
let decrease m =
  try
    Array.iteri (fun i l ->
      match l.(i) with
      | Less -> raise Exit
      | _ -> ()) m;
    false
  with
    Exit -> true

(** Check is a matrice subsumes anothe one (i.e, give less infomation) *)
let subsume m1 m2 =
  try
    Array.iteri (fun i l1 ->
      Array.iteri (fun j x ->
        if not (x >= m2.(i).(j)) then raise Exit) l1) m1;
    true
  with
    Exit -> false

(*****************************************************************************)
(**{2                          The Main algorithm                           }*)
(*****************************************************************************)

(** the main function, checking if calls are well-founded *)
let sct_only : call_table -> bool = fun ftbl ->
  Io.log_sct "SCT starts...\n%!";
  let num_fun = ftbl.current in
  let arities = ftbl.table in
  let tbl = Array.init num_fun (fun _ -> Array.make num_fun []) in
  let print_call ff = print_call ff arities in
  (* counters to count added and composed edges *)
  let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j m =
    (* test idempotent edges as soon as they are discovered *)
    let (_, a, _) = List.assoc i arities in
    if i = j && mat_prod a a a m m = m && not (decrease m) then begin
      Io.log_sct "edge %a idempotent and looping\n%!" print_call (i,j,m,true);
      raise Exit
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
    Io.log_sct "initial edges to be added:\n%!";
    List.iter (fun c -> Io.log_sct "\t%a\n%!" print_call c) ftbl.calls;
    let new_edges = ref ftbl.calls in
    (* compute the transitive closure of the call graph *)
    Io.log_sct "start completion\n%!";
    let rec fn () =
      match !new_edges with
        [] -> ()
      | (i,j,m,_)::l ->
         new_edges := l;
        if add_edge i j m then begin
          Io.log_sct "\tedge %a added\n%!" print_call (i,j,m,true);
          incr added;
          let t' = tbl.(j) in
          Array.iteri (fun k t -> List.iter (fun m' ->
            Io.log_sct "\tcompose: %a * %a = %!"
              print_call (i,j,m,true) print_call (j,k,m',true);
            let (_, a, _) = List.assoc k arities in
            let (_, b, _) = List.assoc j arities in
            let (_, d, _) = List.assoc i arities in
            let m'' = mat_prod a b d m' m in
            incr composed;
            new_edges := (i,k,m'',true) :: !new_edges;
            Io.log_sct "%a\n%!" print_call (i,k,m'',true);
          ) t) t'
        end else
          Io.log_sct "\tedge %a is old\n%!" print_call (i,j,m,true);
        fn ()
    in
    fn ();
    Io.log_sct "SCT passed (%5d edges added, %6d composed)\n%!" !added !composed;
    true
  with Exit ->
    Io.log_sct "SCT failed (%5d edges added, %6d composed)\n%!" !added !composed;
    false

(*****************************************************************************)
(**{2                          Inlining                                     }*)
(*****************************************************************************)

(** Inlining can be deactivated *)
let do_inline = ref true

(** we inline sub-proof when they have only one non recursive call *)
type count = Zero | One of call | More

(** function to count the call according to the above comments     *)
let add_call rec_call n call =
  if rec_call then More else
    match n with
    | Zero -> One call
    | _ -> More

(** inline function that calls only one function. *)
(* TODO: inline function that are called at most once *)
let inline : call_table -> call_table = fun ftbl ->
  if not !do_inline then ftbl else
    let calls = ftbl.calls in
      (* Io.log "before inlining\n";
         List.iter (Io.log "%a\n%!" pr_call) calls; *)
    let tbl = Hashtbl.create 31 in
    List.iter (
      fun (i,j,m,rec_call) ->
        let old = try Hashtbl.find tbl i with Not_found -> Zero in
        let n = add_call rec_call old (i,j,m,true) in
        Hashtbl.replace tbl i n) calls;
    let rec fn (j,i,m,r) =
      try
        match Hashtbl.find tbl i with
        | One (_,k,m',_) ->
           let a = arity k ftbl in
           let b = arity i ftbl in
           let c = arity j ftbl in
           let call = (j,k,mat_prod a b c m' m,r) in
           fn call
        | _ -> (j,i,m,true)
      with Not_found -> (j,i,m,true)
    in
    let calls =
      List.filter (fun (i,j,_,_) -> Hashtbl.find tbl i = More) calls
    in
    let calls = List.map fn calls in
    let rec gn calls =
      let removed_one = ref false in
      let calls =
        List.filter (fun (_,i,_,_) ->
          let b = List.exists (fun (j,_,_,_) -> i = j) calls in
          if not b then removed_one := true;
          b
        ) calls
      in
      if !removed_one then gn calls else calls
    in
    (* Io.log "after inlining\n";
       List.iter (Io.log "%a\n%!" pr_call) calls;*)
    { current = ftbl.current
    ; table   = ftbl.table
    ; calls   = gn calls }

let sct : call_table -> bool = fun tbl -> sct_only (inline tbl)
