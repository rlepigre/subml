(* Church numerals. *)

include "church/bool.typ"
include "church/data.typ"

type CNat = ∀X (X → X) → X → X

val z : CNat =
  fun _ x → x

val s : CNat → CNat =
  fun n f x → f (n f x)

(* First 10 numbers. *)

val 0 : CNat = z
val 1 : CNat = s 0
val 2 : CNat = s 1
val 3 : CNat = s 2
val 4 : CNat = s 3
val 5 : CNat = s 4
val 6 : CNat = s 5
val 7 : CNat = s 6
val 8 : CNat = s 7
val 9 : CNat = s 8

(* Addition and product. *)

val add : CNat → CNat → CNat =
  fun n m f x → n f (m f x)

val mul : CNat → CNat → CNat =
  fun n m f → n (m f)

(* Predecessor functions. *)

val pred  : CNat → CNat =
  fun n → n (fun p x y → p (s x) x) (fun x y → y) z z

val pred2 : CNat → CNat =
  fun n → pi2 (n (fun p →  pair (s (pi1 p)) (pi1 p)) (pair z z))

val pred3 : CNat → CNat =
  fun n → n (fun p x y → p (s x) x) (fun x y → y) z z

(* Comparing functions. *)

val leq : CNat → CNat → CBool =
  fun n m → n (fun f g → g f) (λ_.ctru) (m (fun f g → g f) (λ_.cfls))

val eq : CNat → CNat → CBool = fun n m →
  and (leq n m) (leq m n)

(* Maurey's inferior function. *)

val inf : CNat -> CNat -> CNat =
  fun n m →
    let a =
      fun u m →
        let k = fun c → pair (s (pi1 c)) (s (u (pi1 c))) in
        pi2 (m k (pair z z))
    in
    n a (fun p → z) m

(* Printing function. *)

val printCNat : CNat → {} =
  fun n → n (fun f _ → print("S"); f {}) (fun _ → print("0")) {}

val printlnCNat : CNat → {} =
  fun n → printCNat n; print("\n")

(* Some tests. *)

(*
eval printlnCNat (pred  0)
eval printlnCNat (pred2 0)
eval printlnCNat (pred3 0)

eval printlnCNat (pred  1)
eval printlnCNat (pred2 1)
eval printlnCNat (pred3 1)

eval printlnCNat (pred  8)
eval printlnCNat (pred2 8)
eval printlnCNat (pred3 8)
*)
