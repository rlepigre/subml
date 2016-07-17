(* Chruch encoding for streams without inductive nor coinductive type*)

type Stream(A) = ∀X ((∀S S → (S → S) → (S → A) → X) → X)

val pack : ∀S∀A (S → (S → S) → (S → A) → Stream(A)) = λs f a.(λg.g s f a)

val head : ∀A Stream(A) → A = λs.s (λs1 f a.a s1)

val tail : ∀A Stream(A) → Stream(A) = λs.s (λs1 f a.pack (f s1) f a)

val map = λf s.pack s tail (λs.f (head s))

include "lib/church/data.typ"

val cons : ∀A A → Stream(A) → Stream(A) =
    ΛA λa s.pack (inl a):Sum(A,Stream(A))
              (λx.caseof x (λa.inr s) (λs.inr (tail s)))
              (λx.caseof x (λa.a)     (λs.head s))

include "lib/church/nat.typ"

val all_int = pack 0 (λx.add x 1) (λx.x)


(*this is typable !*)

val get_state : ∀A (Stream(A) → ∃X X) = ΛA λs. s (λs f a.s)
