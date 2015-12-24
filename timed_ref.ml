
type time = { mutable next : time option; undo : unit -> unit; }

let cur_time : time ref = ref { next = None; undo = (fun () -> ()); }

let tref x = { contents = x }

let set : 'a ref -> 'a -> unit = fun p v ->
  let ov = p.contents in
  let undo () = p.contents <- ov in
  assert(!cur_time.next = None);
  let t = { next = None; undo = undo; } in
  !cur_time.next <- Some t;
  cur_time := t;

  p.contents <- v

let ( <:- ) :  'a ref -> 'a -> unit = set

let save_time : unit -> time = fun () -> !cur_time

let undo : time -> unit = fun t ->
  let rec fn = function
    | None -> ()
    | Some t ->
       t.undo (); fn t.next; t.next <- None;
  in
  fn t.next; t.next <- None; cur_time := t

let tincr p = p <:- !p + 1
let tdecr p = p <:- !p - 1

let undo_test f x =
  let time = save_time () in
  let res = f x in
  if not res then undo time;
  res

let pure_test f x =
  let time = save_time () in
  let res = f x in
  undo time;
  res
