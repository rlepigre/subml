(* Scott like encoding for streams with co-inductive type*)
typed; inductive;

include "prod.typ";
include "binary.typ";

type F_Stream(A,K) = ∃S Prod3(S,S→A,S→K);
type Stream(A) = νK F_Stream(A,K);
type GStream(A,S0) = ∃S=S0 νK Prod3(S,S→A,S→K);

let cons = ∀A (fun a:A s:Stream(A) ↦ pair3 (pair a s) pi1 pi2);

let head = ∀A (fun s:Stream(A) ↦ s (λs1 a f.a s1));

let tail = ∀A (fun s:Stream(A) ↦ (s (λs1 a f.f s1)):Stream(A));

type U(A,P) = ∀Y (Prod(P,Y) → A);
type T(A,P) = ∀Y (Prod(P,Y) → Prod3(Prod(P,Y),U(A,P),Y));
type Stream0(P,A) = Prod3(Prod(P,T(A,P)),U(A,P),T(A,P));

(* How to give a deep type indication, working with inductive type *)
type TG(A,P,B) = ∀Y=B (Prod(P,Y) → Prod3(Prod(P,Y),U(A,P),Y));
type StreamG0(P,A,B) = Prod3(Prod(P,T(A,P)),U(A,P),TG(A,P,B));

let test  : ∀A∀P (Stream0(P,A) → Stream(A)) =
  ∀A∀P (fun x:Stream0(P,A) ↦ x :StreamG0(P,A,T(A,P)) : Stream(A));

let coiter = ∀S∀A (fun f:(S → Prod(S,A)) n:S ↦
  (pair3 (pair n
            (fun c ↦ pair3 (pair (pi1 (f (pi1 c))) (pi2 c))
                       (fun c ↦ pi2 (f (pi1 c))) (pi2 c)):T(A,S))
         (fun c ↦ pi2 (f (pi1 c))):U(A,S)
         (fun c ↦ pair3 (pair (pi1 (f (pi1 c))) (pi2 c))
                    (fun c ↦ pi2 (f (pi1 c))) (pi2 c)):T(A,S)) :StreamG0(S,A,T(A,S)) :Stream(A));

type G(A,P) = ∀K ((P → K) → (P → F_Stream(A,K)));

let head' =
  (fun s ↦ s (fun st a f ↦ a st))
  : ∀A∀K (F_Stream(A,K) → A);
let tail' =
  (fun s ↦ s (fun st a f ↦ f st))
  : ∀A∀K (F_Stream(A,K) → K);
let head'' = ∀P∀A (fun f:G(A,P) ↦
  (fun c ↦ head' (f (fun x ↦ x):(P → P) (pi1 c))):U(A,P));
let tail'' = ∀P∀A (fun f:G(A,P) ↦
  (fun c ↦ pair3 (pair (tail' (f (fun x ↦ x):(P → P) (pi1 c))) (pi2 c)) (head'' f) (pi2 c)):T(A,P));

let corec = ∀P∀A (fun f:G(A,P) n:P ↦
  (pair3 (pair n (tail'' f)) (head'' f) (tail'' f)) :StreamG0(P,A,T(A,P)):Stream(A));

let map = ∀A∀B (fun f : (A → B) ↦
  coiter (fun s ↦ pair (tail s) (f (head s))));

let map2 = ∀A∀B (fun f : (A → B) ↦
  corec (∀K fun g:(Stream(A) → K) s:(Stream(A)) ↦ (pair3 s (fun s ↦ f (head s)) (fun s ↦ g (tail s))):F_Stream(B,K)));

let all_ints = coiter (fun n ↦ pair (S n) n) Zero;
let all_ints2 = corec (∀K (fun f:(Bin → K) n:Bin ↦ (pair3 n (fun x ↦ x) (fun n ↦ f (S n))):F_Stream(Bin,K))) Zero;

Print (head all_ints);
Print (head (tail all_ints));
Print (head (tail (tail all_ints)));
Print (head (tail (tail (tail all_ints))));
Print (head (tail (tail (tail (tail all_ints)))));

Print (head all_ints2);
Print (head (tail all_ints2));
Print (head (tail (tail all_ints2)));
Print (head (tail (tail (tail all_ints2))));
Print (head (tail (tail (tail (tail all_ints2)))));

let all_pairs = map (fun x ↦ Mul x 2) all_ints;

Print (head all_pairs);
Print (head (tail all_pairs));
Print (head (tail (tail all_pairs)));
Print (head (tail (tail (tail all_pairs))));
Print (head (tail (tail (tail (tail all_pairs)))));

let all_pairs2 = map2 (fun x ↦ Mul x 2) all_ints;

Print (head all_pairs2);
Print (head (tail all_pairs2));
Print (head (tail (tail all_pairs2)));
Print (head (tail (tail (tail all_pairs2))));
Print (head (tail (tail (tail (tail all_pairs2)))));

let test = ∀A λs:Stream(A). pi1_3 s;
