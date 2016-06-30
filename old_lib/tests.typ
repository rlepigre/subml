typed; inductive; recursive;

fun x:∀X X ↦ x:∃X X;

untyped fun x:∃X X ↦ x:∀X X;

type I = ∀X (X → X);
type I' = ∃X (X → X);

fun x:∀X ((X → X) → (X → X)) ↦ x:(I → I);
fun x:∀X ((X → X) → (X → X)) ↦ x:(I' → I');
fun x:∀X ((X → X) → (X → X)) ↦ x:(I → I');
untyped fun x:∀X ((X → X) → (X → X)) ↦ x:(I' → I);

fun x:(I' → I) ↦ x:∀X ((X → X) → I) ;
fun x:∀X ((X → X) → I) ↦ x:(I' → I) ;
fun x:∃X ((X → X) → I) ↦ x:(I → I) ;
untyped fun x:(I → I) ↦ x:∃X ((X → X) → I) ;

fun x:(I → I) ↦ x:∀X (I → (X → X)) ;
fun x:∀X (I → (X → X)) ↦ x:(I → I) ;
fun x:∃X (I → (X → X)) ↦ x:(I → I') ;
untyped fun x:(I → I') ↦ x:∃X (I → (X → X)) ;

fun x:I ↦ x:∀X∃Y (X → Y);
fun x:I ↦ x:∀X∃Y (Y → X);
fun x:I ↦ x:∃Y∀X (X → Y);
fun x:I ↦ x:∃Y∀X (Y → X);

untyped fun x:∀X∃Y ((Y → X) × (X → Y)) ↦ x:∃Y∀X  ((Y → X) × (X → Y));

let delta = ∃X ∀Y λx:(X → Y).x (x:X); # ne donne pas le bon type
let delta' : ∃X ∀Y ((X → Y) → Y) = ∃X ∀Y λx:(X → Y).x (x:X);

#On active le typage et les types inductifs
typed; inductive;

#type 0 et 1
type Zero = [ ];
let impossible : Zero → ∀X X = fun z ↦ case z of ;

type Zero' = ∀X X;

fun x:Zero ↦ x:Zero';
fun x:Zero' ↦ x:Zero;

type Unit = { };
let unit : Unit = { };

#test du produit

let pair : ∀A∀B (A → B → A × B)
  = fun a b ↦ (a, b);

#booléen
type Bool = [ True | False ];

let neg : Bool → Bool =
  fun b ↦ case b of
        | True[] ↦ False[]
	| False[] ↦ True[] ;

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

let l : ∀X∀Y ((Y → X) → [ A of Y ∪ X ] → X)
  = fun f a ↦ case a of | A[y] ↦ f y | y ↦ y;

let k : ∀X∀Y∀Z ((Y → Z) → [ A of Y ∪ X ] → [ A of Z ∪ X ])
  = fun f a ↦ case a of | A[y] ↦ A[f y] | y ↦ y;


type pos = μX [ S of X | Z ];
type neg = μX [ P of X | Z ];
type rel = [ S of pos | P of neg | Z ];
type rel' = μX [ S of X | P of X | Z ];

fun x:pos ↦ x:rel;
fun x:neg ↦ x:rel;
fun x:rel ↦ x:rel';

untyped fun x:rel ↦ x:pos;
untyped fun x:rel ↦ x:neg;
untyped fun x:rel' ↦ x:rel;

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
  | Z[] ↦ Z[];

let fff x:(∃S S × S) = (x.1, x.2);
