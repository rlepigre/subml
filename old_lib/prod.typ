(* Church encoding of pairs and triplets *)
typed;

type Prod(A, B) = ∀X ((A → B → X) → X);

let pair = (λx y f. f x y) : ∀A ∀B (A → B → Prod(A, B));
let pi1 = ∀A∀B λx : Prod(A,B). (x (λx:A y:B.x));
let pi2 = ∀A∀B λx : Prod(A,B). (x (λx:A y:B.y));

type Prod3(A,B,C) = ∀X ((A → B → C → X) → X);

let pair3 = (λx y z f. f x y z) : ∀A ∀B ∀C (A → B → C → Prod3(A,B,C));
let pi1_3 = ∀A∀B∀C λx : Prod3(A,B,C). (x (λx y z.x));
let pi2_3 = ∀A∀B∀C λx : Prod3(A,B,C). (x (λx y z.y));
let pi3_3 = ∀A∀B∀C λx : Prod3(A,B,C). (x (λx y z.z));


type Sum(A,B) = ∀X ((A → X) → (B → X) → X);
let inl = (λx f g. f x) : ∀A ∀B (A → Sum(A,B));
let inr = (λx f g. g x) : ∀A ∀B (B → Sum(A,B));
let caseof = λx. x;
