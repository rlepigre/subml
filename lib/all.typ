(* Tutorial *)
include "tutorial.typ"

(* Standard library *)
include "lib/nat.typ"
include "lib/list.typ"
include "lib/applist.typ"
include "lib/set.typ"
include "lib/natbin.typ"
include "lib/stream.typ"
include "lib/state_array.typ"

(* Church encoding *)
include "lib/church/bool.typ"
include "lib/church/nat.typ"
include "lib/church/data.typ"
include "lib/church/inf_david.typ"
include "lib/church/error.typ"
include "lib/church/list.typ"
include "lib/church/state.typ"
include "lib/church/stream.typ"

(* Scott encoding *)
include "lib/scott/nat.typ"
include "lib/scott/natbin.typ"
include "lib/scott/list.typ"
include "lib/scott/tree.typ"
include "lib/scott/stream.typ"
include "lib/scott/nat_as_prod.typ"

(* Mixed induction and coinduction *)
include "lib/munu/munu2.typ"
include "lib/munu/munu3.typ"

(* Sorting *)
include "lib/insert_sort.typ"
include "lib/quick_sort.typ"
include "lib/heap.typ"

(* Miscellaneous *)
include "lib/size.typ"
include "lib/hard.typ"
include "lib/lazy_nat.typ"

(* Test files *)
include "lib/dotproj.typ"
include "lib/tree.typ"
include "lib/polyrec.typ"
include "lib/tests.typ"
