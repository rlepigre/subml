type F(X) = [ Z | S of X]
type N = μX F(X)

val rec idt : ∀o ((μo X F(X)) → (μo X F(X))) = fun n →
  case n of
  | Z    → Z
  | S(n) → S(idt n)

val rec idt3 : ∀o (F(μo X F(X)) → F(μo X F(X))) = idt
val rec idt4 : ∀o (μo+1 X F(X)) → μo+1 X F(X) = idt
(*
!val rec idt2 : ∀o (F(μo X F(X)) → F(μo X F(X)))
        = fun n → case n of
          | Z → Z
          | S n → S (idt2 n)
*)
val pred : ∀o [ S of μo X F(X) ] → μo X F(X) = fun n →
  case n of
  | S n → n

val pred' : ∀o (μo+2 X F(X)) → μo+1 X F(X) = fun n →
  case n of
  | Z   → Z
  | S n → n

type G(X) = {} -> [ S of X]

val rec idt' : ∀o (νo X G(X)) → (νo X G(X)) = fun n u →
  case (n {}) of
  | S n → S(idt' n)
(*
!val rec idt2' : ∀o (G(νo X G(X))) → (G(νo X G(X)))
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
