(* l'inf de René David sur les entier de Church ... prove que le typage de René est correct *)
typed;

type Bool = ∀X (X → X → X);
type Nat = ∀X ((X → X) → X → X);
type List(A) = ∀X ((A → X → X) → X → X);
type Nat_Star(O) = ∀X (((X → O) → (X → O)) → (X → O) → (X → O));
type Bool_Star(O) = ∀X ((X → O) → (X → O) → (X → O));
type List_Star(A,O) = ∀X ((A → (X → O) → (X → O)) → (X → O) → (X → O));

let s  : Nat → Nat = λn.λf.λx. (f (n f x));

let zero : Nat = λf.λx. x;

let false  : Bool = λx.λy. y;

let true : Bool = λx.λy. x ;

let nil : ∀X List(X) = λf.λx. x;

let cons : ∀X (X → List(X) → List(X)) = λb.λl.λf.λx. (f b (l f x));

let nstore : ∀O (Nat_Star(O) → (Nat → O) → O) =
  λn. let d1= λf. (f zero) in
      let h1= λx.λy. (x (λz.y (s z))) in
      (n h1 d1);

let bstore : ∀O (Bool_Star(O) → (Bool → O) → O) = λb. (b (λf. f true) (λf. f false));

let lstore  : ∀O (List_Star(Bool,O) → (List(Bool) → O) → O) = ∀O∃X
  λl. let d2 = λf. (f nil) in
      let h2 = λa. (bstore a (λb.λr.λf. r (λz. f (cons b z)))) in
      (l h2 d2);

let test_list : List(Bool) → Nat → Nat → Nat =
  let bB=λb.λr. (b false r) in
  λl.λn.λm. (l bB true n m);

let list : Nat → List(Bool) =
  let cons_0 = λl.λf.λx. (f false (l f x)) in
  λk. (k cons_0 (cons true nil));

let not : Bool → Bool = λa.λx.λy. (a y x);

let pred : List(Bool) → List(Bool) =
  let gG = λa.λy.λb. (b (cons a (y true)) (cons (not a) (y a))) in
  let dD = λb. nil in
  λl. (l gG dD false);

let next : (List(Bool) → Nat) → List(Bool) → Nat =
  λg.λl. (test_list l (s (g l)) (lstore (pred l) g));


let dif : Nat → Nat → Nat =λn.λk. (n next (λx. zero) (list k));

let test : Nat → Nat → Bool → Bool → Bool =λn.λk.λa.λb. (dif n k (λx. a) b);

let init : Nat → Nat → Nat → Nat → Bool =λn.λm.λp.λq. true;

let iteration : (Nat → Nat → Nat → Nat → Bool) → (Nat → Nat → Nat → Nat → Bool) =
  λg.λn.λm.λk.λp.
	(m (λx.
	n (λx. test n k (test m k (g n m (s k) k) false)
          (test m k true ((nstore (dif m p) (nstore (dif n p) g)) zero zero))) true) false);

let inf : Nat → Nat → Bool =λn.λm. (s (s (s ( s (s (s ( s (s n))))))) iteration init n m zero zero);

let good_inf =λn.λm. (inf n m n m);
