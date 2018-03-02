(* Mixed inductive and coinductive types. *)
include "tests/munu2_generated.typ"
include "tests/munu3_generated.typ"

(* Typable examples failing due to the termination check. *)
include "tests/bdd_failing_scp.typ"
include "tests/comb_failing_scp.typ"

(* Example requiring a “max” operator on ordinals. *)
include "tests/max_missing_feature.typ"

(* Examples that must fail. *)
include "tests/delta3_must_fail.typ"

(* Feature tests. *)
include "tests/latex_generation.typ"
