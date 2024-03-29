(** Size change principle. This module implements a decision procedure based
    on the work of Chin Soon Lee, Neil D. Jones and Amir M. Ben-Amram (POPL
    2001). It is used by PML to check that typing and subtyping proofs are
    well-founded. *)

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

(** Index of a function symbol. *)
type index = int

(** Conversion to int. *)
let int_of_index : index -> int = fun i -> i

(** Index of the root. *)
let root : index = -1

(** Map with indices as keys. *)
module IMap =
  struct
    include Map.Make(
      struct
        type t = index
        let compare = compare
      end)

    (** [find k m] will not raise [Not_found] because it will always be used
        when we are sure that the given key [k] is mapped in [m]. *)
    let find : key -> 'a t -> 'a =
      fun k m -> try find k m with Not_found -> assert false
  end

(** A call [{callee; caller; matrix; is_rec}] represents a call to the
    function symbol with key [callee] by the function symbole with the
    key [caller]. The [matrix] gives the relation between the parameters
    of the caller and the callee. The coefficient [matrix.(a).(b)] give
    the relation between the [a]-th parameter of the caller and the
    [b]-th argument of the callee. The boolean [is_rec] is true when the
    call is a reccursive call (i.e. a call to a generalised hypothesis
    lower in the tree. It is [false] for every call to subtyping in the
    typing algorithm and the same goes for rules introducing a new
    induction hypothesis. Every other call refers to a previously
    introduced induction hypothesis and its boolean is [true]. *)
type call =
  { callee : index  (** Key of the function symbol being called. *)
  ; caller : index  (** Key of the calling function symbol. *)
  ; matrix : matrix (** Size change matrix of the call. *)
  ; is_rec : bool   (** Indicates if this is a recursive call. *) }

(** Representation of a function symbol. *)
type symbol =
  { index : index        (** Index for use in a [call]. *)
  ; name  : string       (** Name of the symbol. *)
  ; arity : int          (** Arity of the symbol (number of args). *)
  ; args  : string array (** Name of the arguments. *) }

(** Internal state of the SCT, including the representation of symbols and
    the call graph. *)
type call_graph =
  { next_index : index ref
  ; symbols    : symbol IMap.t ref
  ; calls      : call list ref }

(** Synonym of [call_graph]. *)
type t = call_graph

(** Creation of a new initial [call_graph]. It contains the initial root
    symbol. *)
let create : unit -> t =
  let root = { index = -1 ; name  = "R" ; arity = 0 ; args  = [||] } in
  let syms = IMap.singleton (-1) root in
  fun () -> { next_index = ref 0 ; symbols = ref syms ; calls = ref [] }

(** Creation of a new symbol. The return value is the key of the created
    symbol, to be used in calls. *)
let create_symbol : t -> string -> string array -> index =
  fun g name args ->
    let arity = Array.length args in
    let index = !(g.next_index) in
    let sym = {index ; name ; arity ; args} in
    let open Timed in
    incr g.next_index;
    g.symbols := IMap.add index sym !(g.symbols);
    index

(** Copy a call graph. NOTE not timed. *)
let copy : t -> t =
  fun g ->
    { next_index = ref !(g.next_index)
    ; symbols    = ref !(g.symbols)
    ; calls      = ref !(g.calls) }

(** Test if the call graph is empty. *)
let is_empty : t -> bool =
  fun g -> !(g.calls) = []

(** Add a new call to the call graph. *)
let add_call : t -> call -> unit =
  fun g c -> Timed.(g.calls := c :: !(g.calls))

(** Gives the arity of the symbol corresponding to the given key. The symbol
    must exist. *)
let arity : index -> t -> int =
  fun key g ->
    let sym = IMap.find key !(g.symbols) in
    sym.arity

open Format

let print_call : formatter -> symbol IMap.t -> call -> unit = fun ff tbl c ->
  let caller_sym = IMap.find c.caller tbl in
  let callee_sym = IMap.find c.callee tbl in
  let print_args = LibTools.print_array pp_print_string "," in
  fprintf ff "%s%d(%a%!) <- %s%d%!(" caller_sym.name c.caller
    print_args caller_sym.args callee_sym.name c.callee;
  for i = 0 to callee_sym.arity - 1 do
    if i > 0 then fprintf ff ",";
    let some = ref false in
    for j = 0 to caller_sym.arity - 1 do
      let c = c.matrix.tab.(j).(i) in
      if c <> Infi then
        begin
          let sep = if !some then " " else "" in
          fprintf ff "%s%s%s" sep (cmp_to_string c) caller_sym.args.(j);
          some := true
        end
    done
  done;
  fprintf ff ")%!"

let latex_print_calls ff tbl =
  let arities = IMap.bindings !(tbl.symbols) in
  let calls = !(tbl.calls) in
  fprintf ff "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  let arities = List.filter (fun (j,_) ->
    List.exists (fun c -> j = c.caller || j = c.callee) calls)
    (List.rev arities)
  in
  let numbering = List.mapi (fun i (j,_) -> (j,i)) arities in
  let index j = List.assoc j numbering in
  let not_unique name =
    List.fold_left (fun acc (_,sym) -> if sym.name = name then acc+1 else acc) 0 arities
                   >= 2
  in
  let f (j,sym) =
    if not_unique sym.name then
      fprintf ff "    N%d [ label = \"%s_{%d}\" ];\n" (index j) sym.name (index j)
    else
      fprintf ff "    N%d [ label = \"%s\" ];\n" (index j) sym.name
  in
  List.iter f (List.filter (fun (i,_) ->
    List.exists (fun c -> i = c.caller || i = c.callee) calls) arities);
  let print_call arities {callee = i; caller = j; matrix = m; _} =
    let aj =
      try (List.assoc j arities).arity with Not_found -> assert false
    in
    let ai =
      try (List.assoc i arities).arity with Not_found -> assert false
    in
    fprintf ff "    N%d -> N%d [label = \"\\left(\\begin{smallmatrix}"
      (index j) (index i);

    for j = 0 to aj - 1 do
      if j > 0 then fprintf ff "\\cr\n";
      for i = 0 to ai - 1 do
        if i > 0 then fprintf ff "&";
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

(** the main function, checking if calls are well-founded *)
let sct_only : t -> bool = fun ftbl ->
  Io.log_sct "SCT starts...\n%!";
  let num_fun = !(ftbl.next_index) in
  let arities = !(ftbl.symbols) in
  let tbl = Array.init num_fun (fun _ -> Array.make num_fun []) in
  let print_call ff = print_call ff arities in
  (* counters to count added and composed edges *)
  let added = ref 0 and composed = ref 0 in
  (* function adding an edge, return a boolean indicating
     if the edge is new or not *)
  let add_edge i j m =
    (* test idempotent edges as soon as they are discovered *)
    if i = j && prod m m = m && not (decreasing m) then
      begin
        Io.log_sct "edge %a idempotent and looping\n%!" print_call
          {callee = i; caller = j; matrix = m; is_rec = true};
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
      | [] -> ()
      | {callee = _; caller = j; _}::l when j < 0 -> new_edges := l; fn () (* ignore root *)
      | ({callee = i; caller = j; matrix = m; _} as c)::l ->
        assert (i >= 0);
        new_edges := l;
        if add_edge i j m then begin
          Io.log_sct "\tedge %a added\n%!" print_call c;
          incr added;
          let t' = tbl.(j) in
          Array.iteri (fun k t -> List.iter (fun m' ->
            let c' = {callee = j; caller = k; matrix = m'; is_rec = true} in
            Io.log_sct "\tcompose: %a * %a = %!" print_call c print_call c';
            let m'' = prod m' m in
            incr composed;
            let c'' = {callee = i; caller = k; matrix = m''; is_rec = true} in
            new_edges := c'' :: !new_edges;
            Io.log_sct "%a\n%!" print_call c'';
          ) t) t'
        end else
          Io.log_sct "\tedge %a is old\n%!" print_call c;
        fn ()
    in
    fn ();
    Io.log_sct "SCT passed (%5d edges added, %6d composed)\n%!" !added !composed;
    true
  with Exit ->
    Io.log_sct "SCT failed (%5d edges added, %6d composed)\n%!" !added !composed;
    false

(** Inlining can be deactivated *)
let do_inline = ref true

(** we inline sub-proof when they have only one non recursive call *)
type count = Zero | One of call | More

(** function to count the call according to the above comments     *)
let insert_call rec_call n call =
  if rec_call then More else
    match n with
    | Zero -> One call
    | _ -> More

(** inline function that calls only one function. *)
(* TODO: inline function that are called at most once *)
let inline : t -> t = fun g ->
  if not !do_inline then g else
  let calls = !(g.calls) in
  let tbl = Hashtbl.create 31 in
  let fn c =
    let old = try Hashtbl.find tbl c.callee with Not_found -> Zero in
    let n = insert_call c.is_rec old {c with is_rec = true} in
    Hashtbl.replace tbl c.callee n
  in
  List.iter fn calls;
  let rec fn ({callee = j; caller = i; matrix = m; is_rec = r} as c) =
    try
      match Hashtbl.find tbl i with
      | One {caller = k; matrix = m';_} ->
          fn {callee = j; caller = k; matrix = prod m' m; is_rec = r}
      | _ -> c
    with Not_found -> c
  in
  let calls = List.filter (fun c -> Hashtbl.find tbl c.callee = More) calls in
  let calls = List.map fn calls in
  let rec gn calls =
    let removed_one = ref false in
    let calls =
      let fn {caller;_} =
        let b = List.exists (fun {callee;_} -> caller = callee) calls in
        if not b then removed_one := true; b
      in
      List.filter fn calls
    in
    if !removed_one then gn calls else calls
  in
  { g with calls = ref (gn calls) }

let sct : t -> bool = fun tbl -> sct_only (inline tbl)
