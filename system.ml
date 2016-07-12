exception Stopped

let handle_stop : bool -> unit =
  let open Sys in function
  | true  -> set_signal sigint (Signal_handle (fun i -> raise Stopped))
  | false -> set_signal sigint Signal_default

let clear : unit -> unit =
  fun () -> ignore (Sys.command "clear")

exception Timeout

(* Run a function with a timeout. If the timeout is reached before the end
   of the computation then the exception Timeout is raised. Otherwise
   everything goes the usual way. *)
let timed : int -> ('a -> 'b) -> 'a -> 'b = fun time f x ->
  let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout) in
  let old_behavior = Sys.signal Sys.sigalrm sigalrm_handler in
  let reset_sigalrm () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm old_behavior
  in
  try
    let _ = Unix.alarm time in
    let res = f x in
    reset_sigalrm (); res
  with e -> reset_sigalrm (); raise e
