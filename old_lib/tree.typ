(* Scott like encoding for binary trees with inductive type *)

typed; inductive;

include "binary.typ";

(* Type of trees with data of type A at leaves and data of type B at nodes *)

type F_Tree(A,B,K) = ∀X ((K → B → K → X) → (A → X) → X);
type Tree(A,B) = !K F_Tree(A,B,K);

let leaf = ∀A∀B (fun a:A ↦ (fun f g ↦ g a):Tree(A,B)) ;
let node = ∀A∀B (fun sl:Tree(A,B) b:B sr:Tree(A,B) ↦ (fun f g ↦ f sl b sr):Tree(A,B)) ;

type U(A,P) = ∀Y (A → Y → P);
type T(A,B,P) = ∀Y ((Y → U(A,P) → Y → P) → B → (Y → U(A,P) → Y → P) → Y → P);

let iter = ∀A∀B∀P fun  f:(A → P) g:(P → B → P → P) t:Tree(A,B) ↦
   t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → P)
     (fun sl b sr r ↦ g (sl r (fun a r ↦ f a):U(A,P) r) b (sr r (fun a r ↦ f a):U(A,P) r)) : T(A,B,P)
     (fun a r ↦ f a):U(A,P)
     (fun sl b sr r ↦ g (sl r (fun a r ↦ f a):U(A,P) r) b (sr r (fun a r ↦ f a):U(A,P) r)) : T(A,B,P);

type U(A,B,P) = ∀Y (A → Y → Tree(A,B) → P);
type T(A,B,P) = ∀Y ((Y → U(A,B,P) → Y → Tree(A,B) → P) → B → (Y → U(A,B,P) → Y → Tree(A,B) → P) → Y → Tree(A,B) → P);

let recu = ∀A∀B∀P fun  f:(A → P) g:(Tree(A,B) → P → B → Tree(A,B) → P → P) t:Tree(A,B) ↦
   t:∀P(T(A,B,P) → U(A,B,P) → T(A,B,P) → Tree(A,B) → P)
     (fun sl b sr r tt ↦
        tt (fun slt bt srt ↦ g slt (sl r (fun a r tt ↦ f a):U(A,B,P) r slt) b srt (sr r (fun a r tt ↦ f a):U(A,B,P) r srt))
          (fun at ↦ f at (*impossible*))) : T(A,B,P)
     (fun a r tt ↦ f a):U(A,B,P)
     (fun sl b sr r tt ↦
        tt (fun slt bt srt ↦ g slt (sl r (fun a r tt ↦ f a):U(A,B,P) r slt) b srt (sr r (fun a r tt ↦ f a):U(A,B,P) r srt))
          (fun at ↦ f at (*impossible*))) : T(A,B,P)
     t;

type F2_Tree(A,B,K1,K2) = ∀X ((K1 → B → K2 → X) → (A → X) → X);
type Tree2(A,B) = !K1!K2 F2_Tree(A,B,K1,K2);

let test1 = ∀A∀B (fun t:Tree(A,B)  ↦ t:Tree2(A,B));
let test2 = ∀A∀B (fun t:Tree2(A,B)  ↦ t:Tree(A,B));

type G2(A,B,P) = ∀K1∀K2 ((K1 → P)  → (K2 → P) → F2_Tree(A,B,K1,K2) → P);
type U(A,P) = ∀K1∀K2 (A → K1 → K2 → P);
type T(A,B,P) = ∀K1∀K2 ((K1 → U(A,P) → K1 → K2 → P) → B → (K2 → U(A,P) → K1 → K2 → P) →  K1 → K2 → P);

let leaf' = (fun a f g ↦ g a) :  ∀A∀B∀K1∀K2(A → F2_Tree(A,B,K1,K2));
let node' = ∀A∀B∀K1∀K2(fun sl:K1 b:B sr:K2 ↦ (fun f g ↦ f sl b sr):F2_Tree(A,B,K1,K2));
let leaf'' : ∀A∀B∀P (G2(A,B,P) -> U(A,P)) = fun f a r1 r2 ↦ f (fun x ↦ x) (fun x ↦ x) (leaf' a);
let node'' : ∀A∀B∀P (G2(A,B,P) -> T(A,B,P)) =
   fun f sl b sr r1 r2
  ↦ f (fun r1' ↦ sl r1' (leaf'' f) r1' r2) (fun r2' ↦ sr r2' (leaf'' f) r1 r2') (node' r1 b r2);

let fix2 = ∀A∀B∀P fun  f:G2(A,B,P)  t:Tree(A,B) ↦
   t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → T(A,B,P) → P) (node'' f) (leaf'' f) (node'' f) (node'' f);

type G(A,B,P) = ∀K ((K → P)  → (K → P) → F_Tree(A,B,K) → P);
type U(A,P) = ∀K (A → K → P);
type T(A,B,P) = ∀K ((K → U(A,P) → K → P) → B → (K → U(A,P) → K → P) →  K → P);


let leaf' = (fun a f g ↦ g a) :  ∀A∀B∀K(A → F_Tree(A,B,K));
let node' = ∀A∀B∀K(fun sl:K b:B sr:K ↦ (fun f g ↦ f sl b sr):F_Tree(A,B,K));
let leaf'' : ∀A∀B∀P (G(A,B,P) -> U(A,P)) = fun f a r ↦ f (fun x ↦ x) (fun x ↦ x) (leaf' a);
let node'' : ∀A∀B∀P (G(A,B,P) -> T(A,B,P)) = fun f sl b sr r ↦ f (sl r (leaf'' f)) (sr r (leaf'' f)) (node' r b r);

let fix = ∀A∀B∀P fun  f:G(A,B,P)  t:Tree2(A,B) ↦
   t:∀P(T(A,B,P) → U(A,P) → T(A,B,P) → P) (node'' f) (leaf'' f) (node'' f);

let tree1 = leaf 1;
let tree2 = leaf 2;
let tree3 = leaf 3;
let tree4 = leaf 4;
let tree5 = leaf 5;

let tree375 = node tree3 7 tree5;
let tree154 = node tree1 5 tree4;
let tree1549375 = node tree154 9 tree375;

let sum_all = iter (fun a:Bin ↦ a) (fun l:Bin b:Bin r:Bin ↦ Add (Add l r) b);
let sum_leaf = iter (fun a:Bin ↦ a) (fun l:Bin b:Bin r:Bin ↦ Add l r);
let sum_node = iter (fun a:Bin ↦ 0) (fun l:Bin b:Bin r:Bin ↦ Add (Add l r) b);

Print (sum_all tree1549375);
Print (sum_leaf tree1549375);
Print (sum_node tree1549375);
