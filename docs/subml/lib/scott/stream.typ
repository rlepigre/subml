(* Scott like encoding for streams with co-inductive type*)

include "church/data.typ"
include "scott/nat.typ"

type S_Stream(S,A,K) = Triple(S,S→A,S→K)
type F_Stream(A,K) = ∃S.S_Stream(S,A,K)
type Stream(A) = νK.F_Stream(A,K)
type GStream(A) = ∃S.νK.Triple(S,S→A,S→K)

check GStream([A]) ⊂ Stream([A])

val cons : ∀A.A → Stream(A) → Stream(A) = fun a s →
  let A such that a : A in
  (triple (pair a s) pi1 pi2 : S_Stream(Pair(A,Stream(A)),A,Stream(A)))

val head : ∀A.Stream(A) → A = fun s → s (λs1 a f.a s1)

val tail : ∀A.Stream(A) → Stream(A) = fun s → s (λs1 a f.f s1)

type U(A,P) = ∀Y.(Pair(P,Y) → A)
type T(A,P) = ∀Y.(Pair(P,Y) → Triple(Pair(P,Y),U(A,P),Y))
type Stream0(P,A) = Triple(Pair(P,T(A,P)),U(A,P),T(A,P))

val test  : ∀A.∀P.Stream0(P,A) → Stream(A) =
  fun x →
    let A,P such that x : Stream0(P,A) in
    (x : GStream(A) with S = Pair(P,T(A,P)))

val coiter : ∀S.∀A.(S → Pair(S,A)) → S → Stream(A) =
  fun f n →
    let A,S such that f : S → Pair(S,A) in
    (((triple
      (pair n (fun c → triple (pair (pi1 (f (pi1 c))) (pi2 c))
                       (fun c → pi2 (f (pi1 c))) (pi2 c):T(A,S)))
      (fun c → pi2 (f (pi1 c)) : U(A,S))
      (fun c → triple (pair (pi1 (f (pi1 c))) (pi2 c))
        (fun c → pi2 (f (pi1 c))) (pi2 c) :T(A,S)))
     : Stream0(S,A))
     : GStream(A) with S = Pair(S,T(A,S)))

type G(A,P) = ∀K.((P → K) → (P → F_Stream(A,K)))

val head' : ∀A.∀K.F_Stream(A,K) → A = fun s → s (fun st a f → a st)
val tail' : ∀A.∀K.F_Stream(A,K) → K = fun s → s (fun st a f → f st)

val head'' : ∀P.∀A.G(A,P) → U(A,P) = fun f c → head' (f (fun x → x) (pi1 c))
val tail'' : ∀P.∀A.G(A,P) → T(A,P) = fun f c →
  triple (pair (tail' (f (fun x → x) (pi1 c))) (pi2 c)) (head'' f) (pi2 c)

val corec : ∀P.∀A.G(A,P) → P → Stream(A) =
  fun f n →
    let A,P such that f : G(A,P) in
    (((triple (pair n (tail'' f)) (head'' f) (tail'' f))
      : Stream0(P,A)) : GStream(A) with S = Pair(P,T(A,P)))

val map : ∀A.∀B.(A → B) → Stream(A) → Stream(B) = fun f →
  coiter (fun s → pair (tail s) (f (head s)))

val map2 : ∀A.∀B.(A → B) → Stream(A) → Stream(B) = fun f →
  corec (fun g s → triple s (fun s → f (head s)) (fun s → g (tail s)))

val all_ints : Stream(SNat) = coiter (fun n → pair (s n) n) 0

val all_ints2 : Stream(SNat) = corec (fun f n → triple n (fun x → x) (fun n → f (s n))) 0

eval printu (head all_ints)
eval printu (head (tail all_ints))
eval printu (head (tail (tail all_ints)))
eval printu (head (tail (tail (tail all_ints))))
eval printu (head (tail (tail (tail (tail all_ints)))))

eval printu (head all_ints2)
eval printu (head (tail all_ints2))
eval printu (head (tail (tail all_ints2)))
eval printu (head (tail (tail (tail all_ints2))))
eval printu (head (tail (tail (tail (tail all_ints2)))))

val all_pairs = map (fun x → mul x 2) all_ints

eval printu (head all_pairs)
eval printu (head (tail all_pairs))
eval printu (head (tail (tail all_pairs)))
eval printu (head (tail (tail (tail all_pairs))))
eval printu (head (tail (tail (tail (tail all_pairs)))))

val all_pairs2 = map2 (fun x → mul x 2) all_ints

eval printu (head all_pairs2)
eval printu (head (tail all_pairs2))
eval printu (head (tail (tail all_pairs2)))
eval printu (head (tail (tail (tail all_pairs2))))
eval printu (head (tail (tail (tail (tail all_pairs2)))))

val test : ∀A.Stream(A) → ∃S.S =
  fun s → pi31 s
