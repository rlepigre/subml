type 'a t
val from_val : 'a -> 'a t
val from_fun : 'a t -> ('a -> 'a) -> 'a t
val from_fun2 : 'a t -> 'a t -> ('a -> 'a -> 'a) -> 'a t
val fold : 'a t list -> 'b -> ('b -> 'a -> 'b) -> 'b
val from_funl : 'a t list -> 'a -> ('a -> 'a -> 'a) -> 'a t
val from_ref : 'b ref -> ('b -> 'a t) -> 'a t
val update : 'a t -> unit
val force : 'a t -> 'a
val no_more_build : bool ref
val debug : bool ref
