(* Chruch encoding for streams without inductive nor coinductive type*)
typed;

type Stream(A) = ∀X (∀S (S → (S → S) → (S → A) → X) → X);

type Sum(A,B) = ∀X ((A → X) → (B → X) → X);

let ileft = ∀A∀B λa.(λf g. f a) : Sum(A,B);
let iright = ∀A∀B λb.(λf g. g b) : Sum(A,B);
let caseof = ∀A∀B λs : Sum(A,B) f g.s f g;

let pack = ∀A λs f a.(λg.g s f a) : Stream(A);

let head = ∀A λs:Stream(A).s (λs1 f a.a s1);

let tail = ∀A λs:Stream(A).s (λs1 f a.pack (f s1) f a);

let map = λs f.pack s tail (λs.f (head s));

let cons =∀A λa s.pack (ileft a):Sum(A,Stream(A))
              (λx.caseof x (λa.iright s) (λs.iright (tail s)))
              (λx.caseof x (λa.a)       (λs.head s));

include "nat.typ";

let all_int = pack 0 (λx.add x 1) (λx.x);


(*this is typable !*)

let get_state : ∀A (Stream(A) → ∃X X) = ∀A λs:Stream(A). s (λs f a.s);
