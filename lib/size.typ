type F(X) = [ Z | S of X]
type N = μX F(X)
type NS(α) = μα X F(X)
type NP(α,A) = (A × (μα X F(X))) → {}
type NS'(α) = να X F(X)
type NP'(α,A) = (A × (να X F(X))) → {}

val rec idt : ∀α ((μα X F(X)) → (μα X F(X))) = fun n →
  case n of
  | Z    → Z
  | S(n) → S(idt n)

val rec idt3 : ∀α (F(μα X F(X)) → F(μα X F(X))) = idt
val rec idt4 : ∀α (μα+1 X F(X)) → μα+1 X F(X) = idt
(*
!val rec idt2 : ∀α (F(μα X F(X)) → F(μα X F(X)))
        = fun n → case n of
          | Z → Z
          | S n → S (idt2 n)
*)
val pred : ∀α [ S of μα X F(X) ] → μα X F(X) = fun n →
  case n of
  | S n → n

val pred' : ∀α (μα+2 X F(X)) → μα+1 X F(X) = fun n →
  case n of
  | Z   → Z
  | S n → n

type G(X) = {} -> [ S of X]

val rec idt' : ∀α (να X G(X)) → (να X G(X)) = fun n u →
  case (n {}) of
  | S n → S(idt' n)
(*
!val rec idt2' : ∀α (να+1 X G(X)) → (να+1 X G(X))
        = fun n u → case (n {}) of
          | S n → S (idt2' n)
*)

val rec add : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add x' y)

val rec add' : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → S(add' (idt x') y)

(*
!val rec add'' : N → N → N = fun x y → case x of
  | Z    → y
  | S x' → S(add'' (pred x) y)
*)

val rec add2 : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → add2 x' (S y)

val rec add2' : N → N → N = fun x y →
  case x of
  | Z    → y
  | S x' → add2' (idt x') (S y)

(*
val rec add2'' : N → N → N = fun x y → case x of
  | Z    → y
  | S x' → add2' (pred x) (S y)
*)

val rec mul : N → N → N = fun x y →
  case x of
  | Z    → Z
  | S x' → add (mul x' y) y

(*
val rec mul2 : N → N → N = fun x y → case x of
  | Z → Z
  | S x' → add (mul2 y x') y
*)

type L(α,A) = μα X [Nil | Cons of { hd : A; tl : X}]

val rec map : ∀A ∀B (A → B) → ∀α L(α,A) → L(α,B) =
  fun f l → case l of
    [] → []
  | x::l → f x :: map f l

val rec filter : ∀A ∀B (A → Bool) → ∀α L(α,A) → L(α,A) =
  fun f l → case l of
    [] → []
  | x::l → if f x then x :: filter f l else filter f l

val rec partition : ∀A ∀B (A → Bool) → ∀α L(α,A) → L(α,A) × L(α,A) =
  fun f l → case l of
    [] → ([], [])
  | x::l → let (l1, l2) = partition f l in
           if f x then (x::l1 , l2) else (l1, x::l2)

type L(A) = μ X [Nil | Cons of { hd : A; tl : X}]

val map' = map : ∀A ∀B (A → B) → L(A) → L(B)
val filter' = filter : ∀A (A → Bool) → L(A) → L(A)
val partition' = partition : ∀A (A → Bool) → L(A) → L(A) × L(A)

type S(α,A) = να X {} → { car : A ; cdr : X }

val rec maps : ∀A ∀B (A → B) → ∀α S(α,A) → S(α,B) =
  fun f s _ → let { car = a; cdr = s } = s {} in { car = f a ; cdr = maps f s }

val cons : ∀A ∀α A → S(α,A) → S(α+1,A) =
  fun a s _ →  { car = a; cdr = s }

type S(A) = νX {} → { car : A ; cdr : X }
val maps' = maps : ∀A ∀B (A → B) → S(A) → S(B)

val cons' = cons :∀A ∀B A → S(A) → S(A)
