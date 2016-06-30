(* list using sums encoded as product *)
typed; inductive;
include "nat2.typ";

type List(A) = μ K ∀X ({ Nil : X ; Cons : A × K -> X } -> X);

let nil : ∀A List(A)= \x.x.Nil;

let cons : ∀A (A → List(A) → List(A)) = fun a l x  ↦ x.Cons (a, l);

type T(A,P) = ∀Y (A × ({ Nil : Y → P; Cons : Y } → Y → P) → Y → P);
type List'(A) = ∀P ({Cons : T(A,P) ; Nil : T(A,P) → P } → T(A,P) → P);

let iter_list : ∀A∀P (List(A) → P → (A → P → P) → P) =
  ∀A∀P fun l a f ↦
    let delta : T(A,P) = fun p x ↦ f p.1 (p.2 { Nil = (fun x ↦ a); Cons = x } x) in
    l:List'(A) { Nil = fun x ↦ a; Cons = delta} delta;

let map : ∀A∀B ((A → B) → (List(A) → List(B))) =
  ∀A∀B fun f l ↦ iter_list l nil:List(B) (fun a l ↦ cons (f a) l);

(2, 4).1;

map succ (cons 2 (cons 4 nil));

type T(A,P) = ∀Y (A × ({ Nil : Y → List(A) → P; Cons : Y } → Y → List(A) → P ) → Y → List(A) → P);
type List'(A) = ∀P ({Cons : T(A,P) ; Nil : T(A,P) → List(A) → P } → T(A,P) → List(A) → P);

let cdr : ∀A (List(A) → List(A)) = fun l ↦ l { Nil = nil; Cons = fun l ↦ l.2 };

let rec_list : ∀A∀P (List(A) → P → (List(A) → P → P) → P) =
  ∀A∀P fun l a f ↦
    let delta : T(A,P) = fun p x l ↦ f l (p.2 { Nil = (fun x l ↦ a); Cons = x } x (cdr l)) in
    l:List'(A) { Nil = fun x l ↦ a; Cons = delta} delta l;

type F_List(A,K) = ∀X ({ Nil : X ; Cons : A × K -> X } -> X);
type T(A,P) = ∀Y (A × ({ Nil : Y → P; Cons : Y } → Y → P ) → Y → P);
type List'(A) = ∀P ({Cons : T(A,P) ; Nil : T(A,P) → P } → T(A,P) → P);

let fix_list : ∀A ∀P (∀K ((K → P) → (F_List(A,K) → P)) → (List(A) → P)) =
  ∀A ∀P fun f n  ↦
     let Nil' : ∀Y (Y → P) =
           fun r ↦ f (fun x => x):(∀K K -> P) (\x.x.Nil) in
     let Cons' : T(A,P) =
           fun p r ↦ f (fun s => p.2 { Nil = Nil'; Cons = r } r) (fun x ↦ x.Cons p) in
     (n:List'(A) {Nil = Nil' ; Cons = Cons'}):(T(A,P) → P) Cons';
