(* Church encoding of products and sums. *)

(* Pairs. *)

type Pair(A, B) = ∀X (A → B → X) → X

val pair : ∀A ∀B A → B → Pair(A,B) =
  fun x y f → f x y

val pi1 : ∀A ∀B Pair(A,B) → A =
  fun p → p (fun x y → x)

val pi2 : ∀A ∀B Pair(A,B) → B =
  fun p → p (fun x y → y)

(* Triples. *)

type Triple(A,B,C) = ∀X (A → B → C → X) → X

val triple : ∀A ∀B ∀C A → B → C → Triple(A,B,C) =
  fun x y z p → p x y z

val pi31 : ∀A ∀B ∀C Triple(A,B,C) → A =
  fun p → p (fun x y z → x)

val pi32 : ∀A ∀B ∀C Triple(A,B,C) → B =
  fun p → p (fun x y z → y)

val pi33 : ∀A ∀B ∀C Triple(A,B,C) → C =
  fun p → p (fun x y z → z)

(* Binary disjoint sum. *)

type Sum(A,B) = ∀X (A → X) → (B → X) → X

val inl : ∀A ∀B A → Sum(A,B) =
  fun x f g → f x

val inr : ∀A ∀B B → Sum(A,B) =
  fun x f g → g x

val caseof : ∀A ∀B ∀C Sum(A,B) → (A → C) → (B → C) → C =
  fun x → x
