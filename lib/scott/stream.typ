(* Encoding of streams with co-inductive types and native products *)
include "lib/nat.typ"

type Stream(A) = ν K ∃S { car : S → A; cdr : S → K; state : S}
type Stream0(A,S) = ν K { car : S → A; cdr : S → K; state : S}

val car : ∀A (Stream(A) → A) =  fun s ↦ s.car s.state
val cdr : ∀A (Stream(A) → Stream(A)) = fun s ↦ s.cdr s.state

val scons : ∀A (A → Stream(A) → Stream(A)) =
  fun a l ↦ {car = (fun x ↦ a); cdr = (fun x ↦ l); state = {}}

type T(A,P) = ∀Y (P × Y → { car : P × Y → A; cdr : Y; state : P × Y})

type Stream'(A,P) = { car : P × T(A,P) → A; cdr : T(A,P); state : P × T(A,P)}

val id : ∀A∀P Stream'(A,P) → Stream0(A, P × T(A,P)) = λx.x

val coiter_stream : ∀A∀P (P → (P → A) → (P → P) → Stream(A)) =
  ΛAΛP fun s0 fcar fnext ↦
     let fcar : ∀X (P × X -> A) = fun s ↦ fcar s.1 in
     let delta : T(A,P) = fun s ↦ { car = fcar; cdr = s.2; state = (fnext s.1, s.2) } in
     { car = fcar; cdr = delta; state = (s0, delta) } : Stream'(A,P) : Stream0(A, P × T(A,P))

val int_stream = coiter_stream Z (fun x ↦ x) (fun x ↦ S x)
