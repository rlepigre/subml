include "scott/nat.typ"

(* recursive functions on scotts numerals *)

(* Equality function (using general recursion). *)
val rec eq : SNat → SNat → Bool = fun n m →
  n (fun np → m (fun mp → eq  np mp) fls) (m (fun mp → fls) tru)

(* FIXME: see type.ml, decompose *)
?val rec eqN : SNat → SNat → Bool = fun n m →
  n (fun np → m (fun mp → eqN np mp) Fls) (m (fun mp → Fls) Tru)
