(** Tutorial *)
include "tutorial.typ"

(** Standard library *)

(* simple, common types and function (booleans, option, ...) *)
include "prelude.typ"
(* unary natural numbers *)
include "nat.typ"
(* usual list type *)
include "list.typ"
(* supertype of lists with constant time concatenation *)
include "applist.typ"
(* set with unbalanced binary search tree *)
include "set.typ"
(* binary representation of natural numbers *)
include "natbin.typ"
(* streams (or infinite lists) *)
include "stream.typ"
(* alternative representation of streams, using an internal state *)
include "state_stream.typ"
(* state monad with an association list as state *)
include "state_array.typ"
(* maps implemented using 2-3 trees *)
include "tree23.typ"
(* unary representation of integers (supertype of nat, no trailing zero) *)
include "int.typ"
(* signed digit representation of real numbers (following Alex Simpson) *)
include "real.typ"

(** Sorting functions on lists *)

(* size-preserving insertion sort *)
include "insert_sort.typ"
(* quicksort function *)
include "quick_sort.typ"
(* heapsort function *)
include "heap_sort.typ"

(** Church encoding *)

(* Church-encoded booleans *)
include "church/bool.typ"
(* Church naturals *)
include "church/nat.typ"
(* Church-encoded sums and products *)
include "church/data.typ"
(* Church-encoded lists *)
include "church/list.typ"
(* Church-encoded error monad (option type) *)
include "church/error.typ"
(* Church-encoded state monad *)
include "church/state.typ"
(* Church-encoded streams (infinite lists) *)
include "church/stream.typ"
(* infimum on Church numeral by René David *)
include "church/david.typ"

(** Scott encoding *)

(* Scott-encoded natural numbers *)
include "scott/nat.typ"
(* Scott-encoded lists *)
include "scott/list.typ"
(* Scott-encoded streams (inifinte lists) *)
include "scott/stream.typ"
(* binary representation of natural numbers *)
include "scott/natbin.typ"
(* Scott-like encoded for binary trees *)
include "scott/tree.typ"
(* other encoding Scott naturals using records *)
include "scott/nat_as_prod.typ"

(** Examples *)

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
include "dotproj.typ"
include "dotprojeps.typ"
include "tree.typ"
include "polyrec.typ"
include "permutte.typ"
include "nonterm.typ"
include "failterm.typ"
