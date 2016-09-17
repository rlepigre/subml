include "scott/nat.typ"

(* recursive functions on scotts numerals *)

(* Equality function (using general recursion). *)
val rec eq : SNat → SNat → Bool = fun n m →
  n (fun np → m (fun mp → eq np mp) fls) (m (fun mp → fls) tru)

val rec eqN : SNat → SNat → Bool = fun n m →
  n (λnp. m (λmp. eqN np mp) Fls) (m (λmp. Fls) Tru)
