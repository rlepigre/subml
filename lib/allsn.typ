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
include "scott/nat.typ"
include "scott/list.typ"
include "scott/tree.typ"
include "scott/stream.typ"
include "scott/nat_as_prod.typ"

(* Mixed induction and coinduction *)
include "munu/munu2.typ"
include "munu/munu3.typ"
