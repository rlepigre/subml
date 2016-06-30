(* typed church numeral, very classical *)
typed;

type Nat = ∀X ((X → X) → X → X);

let 0 = (λf x.x) : Nat;
let S = λn:Nat.(λf x.f (n f x)):Nat;
let 1 = S 0; let 2 = S 1; let 3 = S 2; let 4 = S 3;
let 5 = S 4; let 6 = S 5; let 7 = S 6; let 8 = S 7;
let 9 = S 8; let 10 = S 9;
let add = λn:Nat m:Nat.(λf x.n f (m f x)) : Nat;
let mul = λn:Nat m:Nat.(λf.n (m f)):Nat;
let 20 = add 10 10; let 30 = add 20 10;
let 40 = add 30 10; let 100 = mul 10 10;

let pred = λn:Nat.(n
        (λp x y.p (S x) x)
        (λx y.y) 0 0);

include "prod.typ";

let pred = λn:Nat.pi2 (n
        (λp. pair (S (pi1 p)) (pi1 p))
        (pair 0 0));

let pred = λn:Nat.(n
        (λp.p (λx y p.p ((λn:Nat.(λf x.f (n f x))) x) x))
        (λp.p 0 0)):Prod(Nat,Nat) (λx y.y);

include "bool.typ";

inductive; (* this term require inductive types *)

(* inf de Morley *)
let leq = λn:Nat m:Nat. n (λf g.g f) (λi.True)
                        (m (λf g.g f) (λi.False));
