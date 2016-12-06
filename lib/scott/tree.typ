(* Scott like encoding for binary trees with inductive type *)
include "scott/nat.typ"

(* Type of trees with data of type A at leaves and data of type B at nodes *)

type F_Tree(A,B,K) = ∀X ((K → B → K → X) → (A → X) → X)
type Tree(A,B) = μK F_Tree(A,B,K)

val leaf : ∀A∀B (A → Tree(A,B)) =  fun a → (fun f g → g a)
val node : ∀A∀B (Tree(A,B) → B → Tree(A,B) → Tree(A,B)) = fun sl b sr → (fun f g → f sl b sr)

type U(A,P) = ∀Y (A → Y → P)
type T(A,B,P) = ∀Y ((Y → U(A,P) → Y → P) → B → (Y → U(A,P) → Y → P) → Y → P)

val iter : ∀A∀B∀P (A → P) → (P → B → P → P) → Tree(A,B) → P =
 ΛA ΛB ΛP fun f g t →
   t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → P)
     (fun sl b sr r → g (sl r (fun a r → f a):U(A,P) r) b (sr r (fun a r → f a):U(A,P) r)) : T(A,B,P)
     (fun a r → f a):U(A,P)
     (fun sl b sr r → g (sl r (fun a r → f a):U(A,P) r) b (sr r (fun a r → f a):U(A,P) r)) : T(A,B,P)

type U(A,B,P) = ∀Y (A → Y → Tree(A,B) → P)
type T(A,B,P) = ∀Y ((Y → U(A,B,P) → Y → Tree(A,B) → P) → B → (Y → U(A,B,P) → Y → Tree(A,B) → P) → Y → Tree(A,B) → P)

val recu : ∀A∀B∀P (A → P) → (Tree(A,B) → P → B → Tree(A,B) → P → P) → Tree(A,B) → P =
  ΛAΛBΛP fun f g t →
   t:∀P(T(A,B,P) → U(A,B,P) → T(A,B,P) → Tree(A,B) → P)
     (fun sl b sr r tt →
        tt (fun slt bt srt → g slt (sl r (fun a r tt → f a):U(A,B,P) r slt) b srt (sr r (fun a r tt → f a):U(A,B,P) r srt))
          (fun at → f at (*impossible*))) : T(A,B,P)
     (fun a r tt → f a):U(A,B,P)
     (fun sl b sr r tt →
        tt (fun slt bt srt → g slt (sl r (fun a r tt → f a):U(A,B,P) r slt) b srt (sr r (fun a r tt → f a):U(A,B,P) r srt))
          (fun at → f at (*impossible*))) : T(A,B,P)
     t


type F2_Tree(A,B,K1,K2) = ∀X ((K1 → B → K2 → X) → (A → X) → X)
type Tree2(A,B) = μK1 μK2 F2_Tree(A,B,K1,K2)

check Tree([A],[B]) ⊂ Tree2([A],[B])
check Tree2([A],[B]) ⊂ Tree([A],[B])


type G2(A,B,P) = ∀K1∀K2 ((K1 → P)  → (K2 → P) → F2_Tree(A,B,K1,K2) → P)
type U(A,P) = ∀K1∀K2 (A → K1 → K2 → P)
type T(A,B,P) = ∀K1∀K2 ((K1 → U(A,P) → K1 → K2 → P) → B → (K2 → U(A,P) → K1 → K2 → P) →  K1 → K2 → P)


val leaf' : ∀A∀B∀K1∀K2 (A → F2_Tree(A,B,K1,K2)) = (fun a f g → g a)
val node' : ∀A∀B∀K1∀K2 (K1 → B → K2 → F2_Tree(A,B,K1,K2)) = fun sl b sr → (fun f g → f sl b sr)

val leaf'' : ∀A∀B∀P (G2(A,B,P) -> U(A,P)) = fun f a r1 r2 → f (fun x → x) (fun x → x) (leaf' a)
val node'' : ∀A∀B∀P (G2(A,B,P) -> T(A,B,P)) =
   fun f sl b sr r1 r2
  → f (fun r1' → sl r1' (leaf'' f) r1' r2) (fun r2' → sr r2' (leaf'' f) r1 r2') (node' r1 b r2)

val fix2 : ∀A∀B∀P G2(A,B,P) → Tree(A,B) → P = ΛAΛBΛP fun f t →
   t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → T(A,B,P) → P) (node'' f) (leaf'' f) (node'' f) (node'' f)

type G(A,B,P) = ∀K ((K → P)  → (K → P) → F_Tree(A,B,K) → P)
type U(A,P) = ∀K (A → K → P)
type T(A,B,P) = ∀K ((K → U(A,P) → K → P) → B → (K → U(A,P) → K → P) →  K → P)

val leaf' : ∀A∀B∀K(A → F_Tree(A,B,K)) = (fun a f g → g a)
val node' : ∀A∀B∀K(K → B → K → F_Tree(A,B,K)) = fun sl b sr → (fun f g → f sl b sr)
val leaf'' : ∀A∀B∀P (G(A,B,P) -> U(A,P)) = fun f a r → f (fun x → x) (fun x → x) (leaf' a)
val node'' : ∀A∀B∀P (G(A,B,P) -> T(A,B,P)) =
  fun f sl b sr r → f (sl r (leaf'' f)) (sr r (leaf'' f)) (node' r b r)

val fix1 : ∀A∀B∀P (G(A,B,P) → Tree(A,B) → P) = ΛAΛBΛP fun f t →
  t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → P) (node'' f) (leaf'' f) (node'' f)

val tree1 = leaf 1
val tree2 = leaf 2
val tree3 = leaf 3
val tree4 = leaf 4
val tree5 = leaf 5

val tree375 = node tree3 7 tree5
val tree154 = node tree1 5 tree4
val tree1549375 = node tree154 9 tree375

val sum_all = iter (fun (a:SNat) → a) (fun (l:SNat) (b:SNat) (r:SNat) → add (add l r) b)


val sum_leaf = iter (fun (a:SNat) → a) (fun (l:SNat) (b:SNat) (r:SNat) → add l r)
val sum_node = iter (fun (a:SNat) → 0) (fun (l:SNat) (b:SNat) (r:SNat) → add (add l r) b)


eval printu (sum_all tree1549375)
eval printu (sum_leaf tree1549375)
eval printu (sum_node tree1549375)
