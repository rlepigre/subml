
module rec T : sig type 'a t = {
    mutable value : 'a;
    compute : unit -> 'a;
    mutable deps : W.t option;
    mutable is_ref : ('a t * (unit -> 'a t)) option;
    ident: int;
		   }
end
= struct
  type 'a t = {
    mutable value : 'a;
    compute : unit -> 'a;
    mutable deps : W.t option;
    mutable is_ref : ('a t * (unit -> 'a t)) option;
    ident: int;
  }
end
and HashT : Hashtbl.HashedType with type t = Obj.t T.t = struct
  type 'a t0 = 'a T.t
  type t = Obj.t t0
  let equal a b = a.T.ident = b.T.ident
  let hash t = t.T.ident
end

and W : Weak.S with type data = HashT.t = Weak.Make(HashT)

include T

let new_id =
  let r = ref 0 in
  (fun () -> let x = !r in r := x + 1; x)

let no_more_build = ref false
(*
let _ = Sys.(set_signal sigint (Signal_handle (fun _ -> no_more_build := true)))
let check () = if !no_more_build then invalid_arg "no more build"
*)
let (&&&) x y = x && y (* strict and *)

let anon : 'a t -> Obj.t t = Obj.magic

let debug = ref false

let add_deps r x =
  match x.deps with
  | None -> true
  | Some tbl ->
     try ignore (W.find tbl (anon r)); false
     with Not_found ->
       W.add tbl (anon r);
       if !debug then Printf.eprintf "new rule %d\n%!" (W.count tbl);
       false


let iter_deps fn x =
  match x.deps with
  | None -> ()
  | Some tbl -> W.iter (fun v -> fn (Obj.magic v)) tbl

let new_deps () = Some (W.create 31)

let from_val v =
  { value = v; compute = (fun () -> v); deps = None; is_ref = None; ident = new_id () }

let from_fun : 'a t -> ('a -> 'a) -> 'a t = fun l fn ->
  let rec res =
    { value = fn l.value;
      compute = (fun () -> let x = fn l.value in res.value <- x; x);
      deps = new_deps ();
      is_ref = None;
      ident = new_id ()
   }
  in
  if add_deps res l then res.deps <- None;
  res

let from_fun2 : 'a t -> 'a t -> ('a -> 'a -> 'a) -> 'a t = fun l1 l2 fn ->
  let rec res =
    { value = fn l1.value l2.value;
      compute = (fun () -> let x = fn l1.value l2.value in res.value <- x; x);
      deps = new_deps ();
      is_ref = None;
      ident = new_id ()
    }
  in
  if add_deps res l1 &&& add_deps res l2 then res.deps <- None;
  res

let rec fold l a f = match l with
    [] -> a
  | x::l -> fold l (f a x.value) f

let from_funl : 'a t list -> 'a -> ('a -> 'a -> 'a) -> 'a t = fun l a fn ->
  let rec res =
    { value = fold l a fn;
      compute = (fun () -> let x = fold l a fn in res.value <- x; x);
      deps = new_deps ();
      is_ref = None;
      ident = new_id ()
    }
  in
  if List.fold_left (fun b x -> add_deps res x &&& b) true l then res.deps <- None;
  res

let from_ref : 'b ref -> ('b -> 'a t) -> 'a t = fun (l:'b ref) fn ->
  let a = fn (!l) in
  let rec res =
    { value = a.value;
      compute = (fun () -> let x = (fn !l).value in res.value <- x; x);
      deps = new_deps ();
      is_ref = Some (a, fun () -> fn !l);
      ident = new_id ()
    }
  in
  ignore (add_deps res a);
  res

let update : 'a t -> unit = fun b ->
  (match b.is_ref with
    None -> invalid_arg "Fixpoint.update";
  | Some(a,f) ->
     let a' = f () in
     ignore (add_deps b a');
     b.is_ref <- Some (a', f));
  let rec fn x =
    let old = x.value in
    let v = x.compute () in
    if old <> v then begin
      iter_deps fn x
    end
  in fn b

let force : 'a t -> 'a = fun b -> b.value
