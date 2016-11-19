(* Tutorial *)
include "tutorial.typ"

(* Standard library *)
include "nat.typ"
include "list.typ"
include "applist.typ"
include "set.typ"
include "natbin.typ"
include "stream.typ"
include "state_array.typ"
include "tree23.typ"

(* Church encoding *)
include "church/bool.typ"
include "church/nat.typ"
include "church/data.typ"
include "church/inf_david.typ"
include "church/error.typ"
include "church/list.typ"
include "church/state.typ"
include "church/stream.typ"

(* Scott encoding *)
include "scott/natrec.typ"
include "scott/natbin.typ"
include "scott/list.typ"
include "scott/tree.typ"
include "scott/stream.typ"
include "scott/nat_as_prod.typ"

(* Mixed induction and coinduction *)
include "munu/munu2.typ"
include "munu/munu3.typ"

(* Sorting *)
include "insert_sort.typ"
include "quick_sort.typ"
include "heap.typ"

(* Miscellaneous *)
include "size.typ"
include "hard.typ"
include "lazy_nat.typ"

(* Test files *)
include "dotproj.typ"
include "tree.typ"
include "polyrec.typ"
include "tests.typ"
