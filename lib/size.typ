include "prelude.typ"

(** Various tests for size annotations *)

type F(X) = [ Z | S of X]
type N = μX.F(X)
type NS(α) = μα X.F(X)
type NP(α,A) = (A × (μα X.F(X))) → {}
type NS'(α) = να X.F(X)
type NP'(α,A) = (A × (να X.F(X))) → {}

(* good type for succesor *)
val rec succ  : ∀α.NS(α) → NS(α+1) = fun n →
  S (case n of
  | Z    → Z
  | S(n) → succ n)

(* bad type for successor, must fail *)
!val rec succ  : ∀α.NS(α) → NS(α) = fun n →
  let α such that _ : NS(α) in
  (S (case n of
  | Z    → Z
  | S(n) → succ n) : NS(α))

(* various type for predesessor *)
val pred : ∀α.[ S of NS(α) ] → NS(α) = fun n →
  case n of
  | S n → n

(* Z is not typable of type NS(α), hence this pred
   requires this type. Normal, NS(0) is empty *)
val pred' : ∀α.NS(α+2) → NS(α+1) = fun n →
  case n of
  | Z   → Z
  | S n → n

(* identity *)
val rec idt : ∀α.NS(α) → NS(α) = fun n →
  case n of
  | Z    → Z
  | S(n) → S(idt n)

(* fully annotated identity *)
val rec idt2 : ∀α.NS(α) → NS(α) = fun n →
  case n of
  | Z    → Z
  | S(p) → let β such that p : NS(β) in S((idt2 : NS(β) → NS(β)) p)

(* other type (not the best ones) for identity *)
val idt3 : ∀α.F(NS(α)) → F(NS(α)) = idt
val idt4 : ∀α.NS(α+1) → NS(α+1) = idt
val rec idt5 : ∀α.F(NS(α)) → F(NS(α)) = fun n →
  case n of
  | Z → Z
  | S n → S (idt5 n)
val rec idt6 : ∀α.NS(α+1) → NS(α+1) = fun n →
  case n of
  | Z → Z
  | S n → S (idt6 n)

(* Fails, but this is easy to fix, the type of n should be reinforced in the
   S case to exclude Z *)
?val rec idt7 : ∀α.NS(α) → ∀α.NS(α) = fun n →
  case n of
  | Z    → Z
  | S _ → S(idt7 (pred' n))

(* subtraction *)
val rec minus : ∀α β.NS(α) → NS(β) → NS(α) =
  fun n m →
    case n of
    | Z → Z
    | S n' →
       (case m of
       | Z → n
       | S m' → minus n' m')

(* Various recursive successors *)
val rec suc1 : ∀α.NS(α) → NS(α+1) = fun n →
  case n of
  | Z  → S Z
  | S n → S (suc1 n)

val rec suc2 : ∀α.NS(α) → NS(α+2) = fun n →
  case n of
  | Z  → S (S Z)
  | S n →
    let α such that n : NS(α) in
    S (suc2 n : NS(α+2))

(* this one needs unrolling *)
?val rec[1] suc2 : ∀α.NS(α) → NS(α+2) = fun n →
  case n of
  | Z  → S (S Z)
  | S n → S (suc2 n)

val rec suc3 : ∀α.NS(α) → NS(α+3) = fun n →
  case n of
  | Z  → S (S (S Z))
  | S n →
    let α such that n : NS(α) in
    S (suc3 n : NS(α+3))

val rec suc4 : ∀α.NS(α) → NS(α+4) = fun n →
  case n of
  | Z  → S (S (S (S Z)))
  | S n →
    let α such that n : NS(α) in
    S (suc4 n : NS(α+4))

(* various test with addition *)
val rec add : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add x' y)

(* recursive call through identity *)
val rec add2 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add2 (idt x') y)

(* need to know that x is not zero in the second case *)
?val rec add2b : N → N → N = fun x y → case x of
  | Z    → y
  | S x' → S(add2b (pred' x) y)

(* argument permutation *)
val rec add3 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add3 y x')

(* argument permutation and recursice call through identity *)
val rec add4 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add4 y (idt x'))

(* need to know that x is not zero in the second case *)
?val rec add5 : N → N → N = fun x y → case x of
  | Z    → y
  | S x' → S(add5 y (pred x))

(* successor added on the right *)
val rec add6 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → add6 x' (S y)

(* with rec call trough identity *)
val rec add7 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → add7 (idt x') (S y)

(* need to know that x is not zero in the second case *)
?val rec add8 : N → N → N = fun x y → case x of
  | Z    → y
  | S x' → add8 (pred x) (S y)

(* multiplication *)
val rec mul : N → N → N = fun x y →
  case x of
  | Z    → Z
  | S x' → add (mul x' y) y

(* multiplication with argument permutation *)
val rec mul2 : N → N → N = fun x y → case x of
  | Z → Z
  | S x' → add (mul2 y x') y

(* identity on infinite nat *)
type G(X) = {} → [ S of X]

val rec inf_idt : ∀α.(να X.G(X)) → (να X.G(X)) = fun n u →
  case (n {}) of
  | S n → S(inf_idt n)

val rec inf_idt2 : ∀α.(να+1 X.G(X)) → (να+1 X.G(X)) = fun n u →
  case (n {}) of
  | S n → S (inf_idt2 n)

(* Type of lists *)
type L(α,A) = μα X.[Nil | Cons of { hd : A; tl : X}]

val rec map : ∀A B.(A → B) → ∀α.L(α,A) → L(α,B) =
  fun f l → case l of
    [] → []
  | x::l → f x :: map f l

val rec filter : ∀A B.(A → Bool) → ∀α.L(α,A) → L(α,A) =
  fun f l → case l of
    [] → []
  | x::l → if f x then x :: filter f l else filter f l

val rec partition : ∀A B.(A → Bool) → ∀α.L(α,A) → L(α,A) × L(α,A) =
  fun f l → case l of
  | [] → ([], [])
  | x::l →
      let α,A such that l : L(α,A) in (* does not guess the size for c *)
      let ((l1 : L(α,A)), (l2 : L(α,A))) = partition f l in
      if f x then (x::l1 , l2) else (l1, x::l2)

(* lists without size, checking subtyping *)
type L(A) = μX.[Nil | Cons of { hd : A; tl : X}]

val map' : ∀A B.(A → B) → L(A) → L(B) = map

val filter' : ∀A.(A → Bool) → L(A) → L(A) = filter
val partition' : ∀A.(A → Bool) → L(A) → L(A) × L(A) = partition

(* streams *)
type S(α,A) = να X.{} → {car : A; cdr : X}

val rec maps : ∀A B.(A → B) → ∀α.S(α,A) → S(α,B) =
  fun f s _ → let { car = a; cdr = s } = s {} in { car = f a ; cdr = maps f s }

val cons : ∀A.∀α.A → S(α,A) → S(α+1,A) =
  fun a s _ →  { car = a; cdr = s }

(* streams without size, checking subtyping *)
type S(A) = νX.{} → { car : A ; cdr : X }
val maps' : ∀A B.(A → B) → S(A) → S(B) = maps

val cons' : ∀A.A → S(A) → S(A) = cons
