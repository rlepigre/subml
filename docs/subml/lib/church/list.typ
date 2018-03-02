(* Church-encoded lists. *)

include "prelude.typ"
include "church/bool.typ"
include "church/data.typ"
include "church/error.typ"
include "church/nat.typ"

type CList(A) = ∀X ((A → X → X) → X → X)

val nil : ∀A CList(A) =
  fun c n → n

val cns : ∀A A → CList(A) → CList(A) =
  fun e l c n → c e (l c n)

(* Head and tail functions. *)

val car : ∀A CList(A) → Err(A) =
  fun l → l (fun e _ → unit e) error

val cdr : ∀A CList(A) → CList(A) =
  fun l →
    let A such that l : CList(A) in
    l (fun a p x y → p (cns a x) x) snd (nil : CList(A)) (nil : CList(A))

val cdr : ∀A CList(A) → Err(CList(A)) =
  fun l → l (fun _ _ → unit (cdr l)) error

(* Sum of all the element of a list. *)

val sum : CList(CNat) → CNat =
  fun l → l add 0

val assoc : ∀A ∀B (A → A → CBool) → A → CList(Pair(A,B)) → Err(B) =
  fun eq k l → (l (fun y ys → cond (eq k (pi1 y)) (unit (pi2 y)) ys) error)

(* Some tests. *)

val l : CList(Pair(CNat,CNat)) =
  cns (pair 3 4) (cns (pair 5 6) nil)

(*
eval printlnErr printCNat (assoc eq 3 l)
eval printlnErr printCNat (assoc eq 5 l)
eval printlnErr printCNat (assoc eq 4 l)
*)
