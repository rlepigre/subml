
type time

(* same as for reference *)
val set : 'a ref -> 'a -> unit
val ( <:- ) : 'a ref -> 'a -> unit

(* save the current time *)
val save_time : unit -> time

(* undo all affectation up to this time *)
val undo : time -> unit

val tincr : int ref -> unit
val tdecr : int ref -> unit

val undo_test : ('a -> bool) -> 'a -> bool
val pure_test : ('a -> bool) -> 'a -> bool
