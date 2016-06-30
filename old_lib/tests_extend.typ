(* test of extensible record and sums *)
typed;

let x = { a = A[]; b = B[] } : { a : [A] ; b : [B] };

let y : { a : [A'] ; b : [B] } = { x with a = A'[] } ;

y.a : [A'];
untyped y.a : [A];

let f x = (x.1, x.2, x.3);

let g : [ A | B ] → [ A' | B ] = fun a ↦
  case a of | A[] ↦ A'[] | y ↦ y;

let h : ∀X∀Y∀Z ((Y → Z) →
{ X with a : Y } → { X with a : Z }) =
  fun f r ↦ { r with a = f r.a };

let k : ∀X∀Y∀Z ((Y → Z) → [ A of Y ∪ X ] → [ A of Z ∪ X ])
  = fun f a ↦ case a of | A[y] ↦ A[f y] | y ↦ y;

let l : ∀X∀Y ((Y → X) → [ A of Y ∪ X ] → X)
  = fun f a ↦ case a of | A[y] ↦ f y | y ↦ y;

inductive;

type pos = μX [ S of X | Z ];
type neg = μX [ P of X | Z ];
type rel = [ S of pos | P of neg | Z ];
type rel' = μX [ S of X | P of X | Z ];

fun x:pos ↦ x:rel;
fun x:neg ↦ x:rel;

recursive;

let succ:rel → rel = fun x ↦ case x of
| P[x] ↦ x
| y ↦ S[y];

let pred:rel → rel = fun x ↦ case x of
| S[x] ↦ x
| y ↦ P[y];

let rec normal : rel' → rel = fun x ↦
  case x of
  | S[x'] ↦ succ (normal x')
  | P[x'] ↦ pred (normal x')
  | Z ↦ Z;