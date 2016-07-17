(* Church numerals. *)

(* The type of natural numbers and the two basic constructors. *)
type CNat = ∀X (X → X) → X → X

val z : CNat = fun s z → z
val s : CNat → CNat = fun n f x → f (n f x)

(* Names for the first 10 natural numbers. *)
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
val 10: CNat = s 9

(* Addition and product. *)
val add : CNat → CNat → CNat = fun n m f x → n f (m f x)
val mul : CNat → CNat → CNat = fun n m f → n (m f)

(* Printing function. *)
val print_nat : CNat → {} = fun n →
  n (print("S"); (fun x -> x)) (print("Z\n"); {})

(* Predecessor. *)
val pred : CNat → CNat = fun n →
  n (fun p x y → p (s x) x) (fun x y → y) z z

(* Maurey's inferior function. *)
include "lib/church/bool.typ"
val leq : CNat → CNat → CBool = fun n m →
  n (fun f g → g f) (fun i → ctru)
  (m (fun f g → g f) (fun i → cfls))

val eq : CNat → CNat → CBool = fun n m →
  and (leq n m) (leq m n)

include "lib/church/data.typ"
val pred2 : CNat → CNat = fun n → pi2 (n
        (fun p →  pair (s (pi1 p)) (pi1 p))
        (pair z z))

val pred3 : CNat → CNat = fun n → n
        (fun p x y → p (s x) x)
        (fun x y → y) z z

val inf : CNat -> CNat -> CNat = fun n m →
  let a = fun u m →
    let k = λc. pair (s (pi1 c)) (s (u (pi1 c))) in
    pi2 (m k (pair z z))
  in
  n a (λp.z) m

val printCNat : CNat → {} = fun n →
  n (fun f _ → print("s"); f {}) (fun _ → print("0")) {}