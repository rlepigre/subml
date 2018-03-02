(* Mixed inductive and coinductive types. *)
include "tests/munu2_generated.typ"
include "tests/munu3_generated.typ"

(* Typable examples failing due to the termination check. *)
include "tests/bdd_fails.typ"
include "tests/comb_fails.typ"

(* Example requiring a “max” operator on ordinals. *)
include "tests/max_fails.typ"

(* Examples that must fail. *)
include "tests/delta3.typ"
