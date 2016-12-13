include "lib/nat.typ"
include "lib/church/nat.typ"
include "lib/scott/nat.typ"

(* Conversions between Peano numbers and Church numerals. *)
val rec nat_to_church : Nat → CNat =
  fun n →
    case n of
    | Z   → (fun s z → z)
    | S n → (fun f x → f ((nat_to_church n) f x))

val church_to_nat : CNat → Nat =
  fun n → n (fun x → S(x)) Z

(* Conversions between Peano numbers and Scott numerals. *)
val rec nat_to_scott : Nat → SNat =
  fun n →
    case n of
    | Z   → (fun s z → z)
    | S n → (fun s z → s (nat_to_scott n))

val scott_to_nat : SNat → Nat =
  recu Z (fun _ x → S(x))

(* Conversions between Church numerals and Scott numerals. *)
val church_to_scott : CNat → SNat =
  fun n → n (fun n s z → s n) (fun s z → z)

val scott_to_church : SNat → CNat =
  recu (fun s z → z) (fun _ x s z → s (x s z))
