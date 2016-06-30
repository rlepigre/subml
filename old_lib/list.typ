(* list using Church encoding *)
typed; inductive;
include "nat.typ";
include "bool.typ";
include "prod.typ";
include "error.typ";

type List(A) = ∀X ((A → X → X) → X → X);

let nil = (λcs nl.nl) : ∀A List(A);
let cons : ∀A (A → List(A) → List(A)) a l = λcs nl. cs a (l cs nl);

let car : ∀A (List(A) → Err(A)) = ∀A λl:List(A).l (λx y.unit x) Error;

let cdr = ∀A λl:List(A).l
	     (λa p x y.p (cons a x) x)
             (λx y.y) nil nil;


let sum = λl.l:List(Nat) add 0;

let assoc = ∀X∀Y λeq : (X → X → Bool) x l:List(Prod(X,Y)). l
  (λy ys. if (eq x (pi1 y)) (unit (pi2 y)) ys) Error;

(*
let l = cons (pair 3 4) (cons (pair 5 6) nil);
assoc eqN 3 l;
assoc eqN 5 l;
assoc eqN 4 l;
*)
