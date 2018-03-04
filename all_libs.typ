(** Tutorial *)
include "tutorial.typ"

(** Standard library *)

include "prelude.typ"
(* Unary natural numbers *)
include "nat.typ"
(* Linked lists *)
include "list.typ"
(* Lists with an append constructor added (super type of lists) *)
include "applist.typ"
(* Set with unbalanced binary search tree *)
include "set.typ"
(* Binary representation of natural numbers *)
include "natbin.typ"
(* Infinite streams *)
include "stream.typ"
(* Infinite streams with an internal state *)
include "state_stream.typ"
(* The array state monad *)
include "state_array.typ"
(* Map implementation using 2-3 trees *)
include "tree23.typ"
(* Unary representation of integers with nat as a subtype and no trailing zero *)
include "int.typ"
(* Signed digit representation of natural numbers, following Alex Simpson *)
include "real.typ"

(** Sorting *)

(* insertion sort, typed as size preserving *)
include "insert_sort.typ"
(* quick sort, not typed as sized preserving *)
include "quick_sort.typ"
(* heap sort, not typed as sized preserving *)
include "heap.typ"

(** Miscellaneous *)

(* various tests with subtyping on fixpoint *)
include "subfix.typ"
(* various tests with sized type and termination *)
include "size.typ"
(* an accepted function not passing the semi-continuous condition *)
include "hard.typ"
(* a little code on lazy naturals (interesting for termination) *)
include "lazy_nat.typ"
(* filter on stream, using μ and ν mixed type *)
include "stream_filter.typ"
(* ordinal (an inductive type that converges slowly) with two additions *)
include "ordinal.typ"
include "lambda.typ"
include "simply.typ"

(** Church encoding *)
include "church/bool.typ"
include "church/nat.typ"
include "church/data.typ"
(* infimum on Church's numeral by Ren&eacute; David *)
include "church/david.typ"
include "church/error.typ"
include "church/list.typ"
include "church/state.typ"
include "church/stream.typ"

(** Scott encoding *)
include "scott/nat.typ"
include "scott/natbin.typ"
include "scott/list.typ"
include "scott/tree.typ"
include "scott/stream.typ"
include "scott/nat_as_prod.typ"

(** Test files *)
include "dotproj.typ"
include "dotprojeps.typ"
include "tree.typ"
include "polyrec.typ"
include "permutte.typ"
include "nonterm.typ"
include "failterm.typ"
