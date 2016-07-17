(* Scott like encoding for streams with co-inductive type*)

include "lib/church/data.typ"
include "lib/scott/natbin.typ"

type F_Stream(A,K) = ∃S Triple(S,S→A,S→K)
type Stream(A) = νK F_Stream(A,K)
type GStream(A,S0) = νK Triple(S0,S0→A,S0→K)

val cons : ∀A A → Stream(A) → Stream(A) = fun a s → triple (pair a s) pi1 pi2

val head : ∀A Stream(A) → A = fun s → s (λs1 a f.a s1)

val tail : ∀A Stream(A) → Stream(A) = fun s → s (λs1 a f.f s1)

type U(A,P) = ∀Y (Pair(P,Y) → A)
type T(A,P) = ∀Y (Pair(P,Y) → Triple(Pair(P,Y),U(A,P),Y))
type Stream0(P,A) = Triple(Pair(P,T(A,P)),U(A,P),T(A,P))

(* FIXME …. TG below …
(* How to give a deep type indication, working with inductive type *)
type TG(A,P,B) = ∀Y=B (Pair(P,Y) → Triple(Pair(P,Y),U(A,P),Y))
type StreamG0(P,A,B) = Triple(Pair(P,T(A,P)),U(A,P),TG(A,P,B))

val test  : ∀A∀P (Stream0(P,A) → Stream(A)) =
  ΛAΛP (fun (x:Stream0(P,A)) → (x :StreamG0(P,A,T(A,P))))

val coiter = ∀S∀A (fun f:(S → Pair(S,A)) n:S →
  (triple (pair n
            (fun c → triple (pair (pi1 (f (pi1 c))) (pi2 c))
                       (fun c → pi2 (f (pi1 c))) (pi2 c)):T(A,S))
         (fun c → pi2 (f (pi1 c))):U(A,S)
         (fun c → triple (pair (pi1 (f (pi1 c))) (pi2 c))
                    (fun c → pi2 (f (pi1 c))) (pi2 c)):T(A,S)) :StreamG0(S,A,T(A,S)) :Stream(A))

type G(A,P) = ∀K ((P → K) → (P → F_Stream(A,K)))

val head' =
  (fun s → s (fun st a f → a st))
  : ∀A∀K (F_Stream(A,K) → A)
val tail' =
  (fun s → s (fun st a f → f st))
  : ∀A∀K (F_Stream(A,K) → K)
val head'' = ∀P∀A (fun f:G(A,P) →
  (fun c → head' (f (fun x → x):(P → P) (pi1 c))):U(A,P))
val tail'' = ∀P∀A (fun f:G(A,P) →
  (fun c → triple (pair (tail' (f (fun x → x):(P → P) (pi1 c))) (pi2 c)) (head'' f) (pi2 c)):T(A,P))

val corec = ∀P∀A (fun f:G(A,P) n:P →
  (triple (pair n (tail'' f)) (head'' f) (tail'' f)) :StreamG0(P,A,T(A,P)):Stream(A))

val map = ∀A∀B (fun f : (A → B) →
  coiter (fun s → pair (tail s) (f (head s))))

val map2 = ∀A∀B (fun f : (A → B) →
  corec (∀K fun g:(Stream(A) → K) s:(Stream(A)) → (triple s (fun s → f (head s)) (fun s → g (tail s))):F_Stream(B,K)))

val all_ints = coiter (fun n → pair (S n) n) Zero
val all_ints2 = corec (∀K (fun f:(Bin → K) n:Bin → (triple n (fun x → x) (fun n → f (S n))):F_Stream(Bin,K))) Zero

Print (head all_ints)
Print (head (tail all_ints))
Print (head (tail (tail all_ints)))
Print (head (tail (tail (tail all_ints))))
Print (head (tail (tail (tail (tail all_ints)))))

Print (head all_ints2)
Print (head (tail all_ints2))
Print (head (tail (tail all_ints2)))
Print (head (tail (tail (tail all_ints2))))
Print (head (tail (tail (tail (tail all_ints2)))))

val all_pairs = map (fun x → Mul x 2) all_ints

Print (head all_pairs)
Print (head (tail all_pairs))
Print (head (tail (tail all_pairs)))
Print (head (tail (tail (tail all_pairs))))
Print (head (tail (tail (tail (tail all_pairs)))))

val all_pairs2 = map2 (fun x → Mul x 2) all_ints

Print (head all_pairs2)
Print (head (tail all_pairs2))
Print (head (tail (tail all_pairs2)))
Print (head (tail (tail (tail all_pairs2))))
Print (head (tail (tail (tail (tail all_pairs2)))))

val test = ∀A λs:Stream(A). pi1_3 s
*)