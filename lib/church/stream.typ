(* Church encoding for streams (no inductive or coinductive type). *)

include "church/data.typ"
include "church/nat.typ"

type CStream(A) = ∀X (∀S S → (S → S) → (S → A) → X) → X

val pack : ∀S ∀A S → (S → S) → (S → A) → CStream(A) =
  fun s f a g → g s f a

(* Head and tail functions. *)

val head : ∀A CStream(A) → A =
  fun s → s (fun s _ a → a s)

val tail : ∀A CStream(A) → CStream(A) =
  fun s → s (fun s f a → pack (f s) f a)

(* Cons function. *)

val cons : ∀A A → CStream(A) → CStream(A) =
  fun e s →
    pack (inl e)
      (fun x → caseof x (fun _ → inr s) (fun s → inr (tail s)))
      (fun x → caseof x (fun e → e    ) (fun s → head s))

(* Map function. *)

val map : ∀A ∀B (A → B) → CStream(A) → CStream(B) =
  fun f s → pack s tail (fun s → f (head s))

(* CStream of all the church naturals. *)

val all_ints : CStream(CNat) =
  pack 0 (fun e → add e 1) (fun e → e)

(* Surprisingly, we can extract the internal state of the stream. *)

val get_state : ∀A CStream(A) → ∃X X =
  fun s → s (fun s _ _ → s)
