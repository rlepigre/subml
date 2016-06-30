typed; inductive; recursive;

type F(X) = [ Z | S of X ];
type G(X) = [ Z | S of X | P of X ];

let test : ∀[a] (μ[a] X F(X) → μ[a] X G(X)) = fun x ↦ x;
let test2 : ∀[a] (μ[a] X F(X) → μ[a] X G(G(X))) = fun x ↦ x;
untyped (fun x ↦ x) : ∀[a] (μ[a] X F(F(X)) → μ[a] X G(X));

type N = μX F(X);

let rec idt : ∀[a] (μ[a] X F(X) → μ[a] X F(X)) =
  fun x ↦ case x of
    Z[] ↦ Z[]
  | S[x] ↦ S[idt x];

let idt' = idt : N → N;

let pred :  ∀[a] (F(F(μ[a] X F(X))) → F(μ[a] X F(X))) =
  fun x ↦ case x of
    Z[] ↦ Z[]
  | S[x] ↦ x;

let pred' = pred : N → N;

type FL(A,X) = [Nil | Cons of A × X];
type L(A) = μX FL(A,X);

let rec map : ∀A ∀B ((A → B) → ∀[a] (μ[a]X FL(A,X) → μ[a]X FL(B,X))) =
  fun f l ↦ case l of
    Nil[] ↦ Nil[]
  | Cons[t] ↦ Cons[f t.1, map f t.2];

let rec filter : ∀A ∀B ((A → [T|F]) → ∀[a] (μ[a]X FL(A,X) → μ[a]X FL(A,X))) =
  fun f l ↦ case l of
    Nil[] ↦ Nil[]
  | Cons[t] ↦ (case f t.1 of
      | T[] ↦ Cons[t.1, filter f t.2]
      | F[] ↦ filter f t.2);

let rec partition : ∀A ∀B ((A → [T|F]) → ∀[a] (μ[a]X FL(A,X) → (μ[a]X FL(A,X)) × (μ[a]X FL(A,X)))) =
  fun f l ↦ case l of
    Nil[] ↦ (Nil[], Nil[])
  | Cons[t] ↦ let r = partition f t.2 in (case f t.1 of
      | T[] ↦ (Cons[t.1, r.1], r.2)
      | F[] ↦ (r.1, Cons[t.1, r.2]));

let map' = map : ∀A ∀B ((A → B) → (L(A) → L(B)));
let filter' = filter : ∀A ((A → [T|F]) → (L(A) → L(A)));
let partition' = partition : ∀A ((A → [T|F]) → (L(A) → L(A) × L(A)));

type FS(A,X) = { car : A ; cdr : X };
type S(A) = νX FS(A,X);

let rec maps : ∀A ∀B ((A → B) → ∀[a] (ν[a]X FS(A,X) → ν[a]X FS(B,X))) =
  fun f s ↦ { car = f s.car ; cdr = maps f s.cdr };

let maps' = maps : ∀A ∀B ((A → B) → S(A) → S(B));

let cons : ∀A ∀[a] (A → ν[a]X FS(A,X) → FS(A,ν[a]X FS(A,X))) =
  fun a s ↦ { car = a; cdr = s };

let cons' = cons :∀A ∀B (A → S(A) → S(A));

(*
Faux pas rêver:

let y : ∀X (∀[a] (∀[b<a] μ[b] X (F(X) → X) → (μ[a] X F(X) → X)) → (N → X)) =
  fun f ↦ (fun x ↦ f (x x)) (fun x ↦ f (x x));
*)