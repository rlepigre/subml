(* list using Church encoding *)

include "church/nat.typ"
include "church/bool.typ"
include "church/data.typ"
include "church/error.typ"

type List(A) = ∀X ((A → X → X) → X → X)

val nil = (λcs nl.nl) : ∀A List(A)
val cons : ∀A (A → List(A) → List(A)) = fun a l → λcs nl. cs a (l cs nl)

val car : ∀A (List(A) → Err(A)) = ΛA λ(l:List(A)).l (λx y.unit x) error

val cdr : ∀A (List(A) → List(A)) =
        ΛA λ(l:List(A)).l
             (λa p x y.p (cons a x) x)
             (λx y.y) (nil:List(A)) (nil:List(A))


val sum = λl.l:List(CNat) add 0

val assoc : ∀A∀B (A → A → CBool) → A → List(Pair(A,B)) → Err(B) = λeq x l. (l
  (λy ys. cond (eq x (pi1 y)) (unit (pi2 y)) ys) error)


val l = cons (pair 3 4) (cons (pair 5 6) nil)

eval printErr printCNat (assoc eq 3 l)
eval printErr printCNat (assoc eq 5 l)
eval printErr printCNat (assoc eq 4 l)
