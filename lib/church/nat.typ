(* Church numerals. *)

(* The type of natural numbers and the two basic constructors. *)
type CNat = ∀X (X → X) → X → X

val z : CNat = fun s z ↦ z
val s : CNat → CNat = fun n f x ↦ f (n f x)

(* Names for the first 10 natural numbers. *)
val zero  : CNat = z
val one   : CNat = s zero
val two   : CNat = s one
val three : CNat = s two
val four  : CNat = s three
val five  : CNat = s four
val six   : CNat = s five
val seven : CNat = s six
val eight : CNat = s seven
val nine  : CNat = s eight
val ten   : CNat = s nine

(* Addition and product. *)
val add : CNat → CNat → CNat = fun n m f x ↦ n f (m f x)
val mul : CNat → CNat → CNat = fun n m f ↦ n (m f)

(* Printing function. *)
val print_nat : CNat → {} = fun n ↦
  n (print("S"); (fun x -> x)) (print("Z\n"); {})

(* Predecessor. *)
val pred : CNat → CNat = fun n ↦
  n (fun p x y ↦ p (s x) x) (fun x y ↦ y) z z

(* Maurey's inferior function. *)
include "lib/church/bool.typ"
val leq : CNat → CNat → CBool = fun n m ↦
  n (fun f g ↦ g f) (fun i ↦ ctru)
  (m (fun f g ↦ g f) (fun i ↦ cfls))


include "lib/church/data.typ"
val pred2 : CNat → CNat = fun n ↦ pi2 (n
        (fun p ↦  pair (s (pi1 p)) (pi1 p))
        (pair z z))

val pred3 : CNat → CNat = fun n ↦ n
        (fun p x y ↦ p (s x) x)
        (fun x y ↦ y) z z

val inf : CNat -> CNat -> CNat = fun n m ↦
  let a = fun u m ↦
    let k = λc. pair (s (pi1 c)) (s (u (pi1 c))) in
    pi2 (m k (pair z z))
  in
  n a (λp.z) m
