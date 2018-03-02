include "church/bool.typ"
include "scott/nat.typ"

(* recursive functions on scotts numerals *)

(* Equality function (using general recursion). *)
val rec eq : SNat → SNat → CBool = fun n m →
  n (fun np → m (fun mp → eq  np mp) cfls) (m (fun mp → cfls) ctru)

(* harder: must guess type of bool *)
val rec eqN : SNat → SNat → CBool = fun n m →
  n (fun np → m (fun mp → eqN np mp) cfls) (m (fun mp → cfls) ctru)
