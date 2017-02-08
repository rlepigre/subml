(** Size change principle. This module implements a decision procedure based
    on the work of Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL
    2001). It is used by PML to check that typing and subtyping proofs are
    well-founded. *)

(** Map with integer keys. *)
module IMap = Map.Make(
  struct
    type t = int
    let compare = compare
  end)

(** Representation of the set {-1, 0, ∞} *)
type cmp = Min1 | Zero | Infi

(** String representation. *)
let cmp_to_string : cmp -> string =
  function Min1 -> "<" | Zero -> "=" | Infi -> "?"

(** Addition operation (minimum) *)
let (<+>) : cmp -> cmp -> cmp = min

(** Multiplication operation. *)
let (<*>) : cmp -> cmp -> cmp = fun e1 e2 ->
  match (e1, e2) with
  | (Infi, _   ) | (_   , Infi) -> Infi
  | (Min1, _   ) | (_   , Min1) -> Min1
  | (Zero, Zero) -> Zero

(** Type of a size change matrix. *)
type matrix =
  { w   : int
  ; h   : int
  ; tab : cmp array array }

(** Matrix product. *)
let prod : matrix -> matrix -> matrix = fun m1 m2 ->
  assert (m1.w = m2.h);
  let tab =
    Array.init m1.h (fun y ->
      Array.init m2.w (fun x ->
        let r = ref Infi in
        for k = 0 to m1.w - 1 do
          r := !r <+> (m1.tab.(y).(k) <*> m2.tab.(k).(x))
        done; !r
      )
    )
  in
  { w = m2.w ; h = m1.h ; tab }

(** Check if a matrix corresponds to a decreasing idempotent call. *)
let decreasing : matrix -> bool = fun m ->
  assert (m.w = m.h);
  try
    for k = 0 to m.w - 1 do
      if m.tab.(k).(k) = Min1 then raise Exit
    done; false
  with Exit -> true

(** Check if a matrix subsumes another one (i.e. gives more infomation). *)
let subsumes : matrix -> matrix -> bool = fun m1 m2 ->
  try
    Array.iteri (fun y l ->
      Array.iteri (fun x e ->
        if not (e >= m2.tab.(y).(x)) then raise Exit
      ) l
    ) m1.tab; true
  with Exit -> false





type index = int (** index of a function *)
type call = index * index * matrix * bool
type calls = call list
type symbol = string * int * string array

let call_index : call -> index =
  fun (i, _, _, _) -> i

(** This stores the function table, giving name, arity and the
    way to print the function for debugging *)
type arities = (int * symbol) list
type call_table =
  { current : int ref
  ; table   : arities ref
  ; calls   : calls ref }

type t = call_table

(** Initialisation of a new function table *)
let init_table () =
  { current = ref 0
  ; table   = ref [(-1, ("R", 0, [||]))] (* the root call is predefined *)
  ; calls   = ref [] }

(** the root index *)
let root = -1

(** Creation of a new function, return the function index in the table *)
let new_function : call_table -> string -> string list -> index =
  fun ftbl name args ->
    let args = Array.of_list args in
    let arity = Array.length args in
    let n = !(ftbl.current) in
    let open Timed in
    ftbl.current := n + 1;
    ftbl.table   := (n, (name, arity, args))::!(ftbl.table);
    n

let new_call : call_table -> call -> unit = fun tbl call ->
  Timed.(tbl.calls := call::!(tbl.calls))

(** Gives the arity of a given function *)
let arity : int -> call_table -> int = fun i ftbl ->
  try let (_,a,_) = List.assoc i !(ftbl.table) in a
  with Not_found -> assert false

let copy t = { current = ref !(t.current)
             ; table   = ref !(t.table)
             ; calls   = ref !(t.calls) }

let is_empty tbl = !(tbl.calls) = []

(*****************************************************************************)
(**{2               Printing functions for debugging                        }*)
(*****************************************************************************)

open Format

let prInd ff = fprintf ff "%d"
let strInd = string_of_int
let prCmp ff c = pp_print_string ff (cmp_to_string c)

let print_call : formatter -> (int * symbol) list -> call -> unit =
  fun ff tbl (i,j,m,_) ->
    let (namej,aj,prj) =
      try List.assoc j tbl with Not_found -> assert false
    in
    let (namei,ai,_  ) =
      try List.assoc i tbl with Not_found -> assert false
    in
    let print_args = LibTools.print_array pp_print_string "," in
    fprintf ff "%s%d(%a%!) <- %s%d%!(" namej j print_args prj namei i;
    for i = 0 to ai - 1 do
      if i > 0 then fprintf ff ",";
      let some = ref false in
      for j = 0 to aj - 1 do
        let c = m.tab.(j).(i) in
        if c <> Infi then
          begin
            let sep = if !some then " " else "" in
            fprintf ff "%s%a%s" sep prCmp c prj.(j);
            some := true
          end
      done
    done;
    fprintf ff ")%!"

let latex_print_calls ff tbl =
  let arities = !(tbl.table) in
  let calls = !(tbl.calls) in
  fprintf ff "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  let arities = List.filter (fun (j,_) ->
    List.exists (fun (i1,i2,_,_) -> j = i1 || j = i2) calls)
    (List.rev arities)
  in
  let numbering = List.mapi (fun i (j,_) -> (j,i)) arities in
  let index j = List.assoc j numbering in
  let not_unique name =
    List.fold_left (fun acc (_,(n,_,_)) -> if n = name then acc+1 else acc) 0 arities
                   >= 2
  in
  let f (j,(name,_,_)) =
    if not_unique name then
      fprintf ff "    N%d [ label = \"%s_{%d}\" ];\n" (index j) name (index j)
    else
      fprintf ff "    N%d [ label = \"%s\" ];\n" (index j) name
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
    fprintf ff "    N%d -> N%d [label = \"\\left(\\begin{smallmatrix}"
      (index j) (index i);
    for i = 0 to ai - 1 do
      if i > 0 then fprintf ff "\\cr\n";
      for j = 0 to aj - 1 do
        if j > 0 then fprintf ff "&";
        let c =
          match m.tab.(j).(i) with
          | Infi -> "\\infty"
          | Zero -> "0"
          | Min1 -> "-1"
        in
        fprintf ff "%s" c
      done;
    done;
    fprintf ff "\\end{smallmatrix}\\right)\"]\n%!"
  in
  List.iter (print_call arities) calls;
  fprintf ff "  }\n\\end{dot2tex}\n"

(*****************************************************************************)
(**{2                          The Main algorithm                           }*)
(*****************************************************************************)

(** the main function, checking if calls are well-founded *)
let sct_only : call_table -> bool = fun ftbl ->
  Io.log_sct "SCT starts...\n%!";
  let num_fun = !(ftbl.current) in
  let arities = !(ftbl.table) in
  let tbl = Array.init num_fun (fun _ -> Array.make num_fun []) in
  let print_call ff = print_call ff arities in
  (* counters to count added and composed edges *)
  let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j m =
    (* test idempotent edges as soon as they are discovered *)
    if i = j && prod m m = m && not (decreasing m) then begin
      Io.log_sct "edge %a idempotent and looping\n%!" print_call (i,j,m,true);
      raise Exit
    end;
    let ti = tbl.(i) in
    let ms = ti.(j) in
    if List.exists (fun m' -> subsumes m' m) ms then
      false
    else (
      let ms = m :: List.filter (fun m' -> not (subsumes m m')) ms in
      ti.(j) <- ms;
      true)
  in
  (* adding initial edges *)
  try
    Io.log_sct "initial edges to be added:\n%!";
    List.iter (fun c -> Io.log_sct "\t%a\n%!" print_call c) !(ftbl.calls);
    let new_edges = ref !(ftbl.calls) in
    (* compute the transitive closure of the call graph *)
    Io.log_sct "start completion\n%!";
    let rec fn () =
      match !new_edges with
        [] -> ()
      | (i,j,_,_)::l when j < 0 -> new_edges := l; fn () (* ignore root *)
      | (i,j,m,_)::l ->
        assert (i >= 0);
        new_edges := l;
        if add_edge i j m then begin
          Io.log_sct "\tedge %a added\n%!" print_call (i,j,m,true);
          incr added;
          let t' = tbl.(j) in
          Array.iteri (fun k t -> List.iter (fun m' ->
            Io.log_sct "\tcompose: %a * %a = %!"
              print_call (i,j,m,true) print_call (j,k,m',true);
            let m'' = prod m' m in
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
    let calls = !(ftbl.calls) in
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
           let call = (j,k,prod m' m,r) in
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
    { current = ftbl.current
    ; table   = ftbl.table
    ; calls   = ref (gn calls) }

let sct : call_table -> bool = fun tbl -> sct_only (inline tbl)
