(* Standard library. *)
include "lib/nat.typ"
include "lib/list.typ"
include "lib/applist.typ"
include "lib/set.typ"
include "lib/natbin.typ"

(* Church encoding. *)
include "lib/church/bool.typ"
include "lib/church/nat.typ"
include "lib/church/data.typ"
include "lib/church/inf_david.typ"
include "lib/church/error.typ"

(* Scott encoding. *)
include "lib/scott/nat.typ"
include "lib/scott/stream.typ"

(* Test files. *)
include "lib/dotproj.typ"
include "lib/tree.typ"
include "lib/polyrec.typ"

(* Subtyping tests. *)
include "lib/tests.typ"

(* Mixed induction and coinduction. *)
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
