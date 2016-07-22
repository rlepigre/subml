(* l'inf de René David sur les entier de Church ... prove que le typage de René est correct *)
include "church/bool.typ"

type Nat = ∀X ((X → X) → X → X)
type List(A) = ∀X ((A → X → X) → X → X)
type Nat_Star(O) = ∀X (((X → O) → (X → O)) → (X → O) → (X → O))
type CBool_Star(O) = ∀X ((X → O) → (X → O) → (X → O))
type List_Star(A,O) = ∀X ((A → (X → O) → (X → O)) → (X → O) → (X → O))

val s  : Nat → Nat = λn.λf.λx. (f (n f x))

val zero : Nat = λf.λx. x

val nil : ∀X List(X) = λf.λx. x

val cons : ∀X (X → List(X) → List(X)) = λb.λl.λf.λx. (f b (l f x))

val nstore : ∀O (Nat_Star(O) → (Nat → O) → O) =
  λn. let d1= λf. (f zero) in
      let h1= λx.λy. (x (λz.y (s z))) in
      (n h1 d1)

val bstore : ∀O (CBool_Star(O) → (CBool → O) → O) = λb. (b (λf. f ctru) (λf. f cfls))

val lstore  : ∀O (List_Star(CBool,O) → (List(CBool) → O) → O) =
  λl. let d2 = λf. (f nil) in
      let h2 = λa. (bstore a (λb.λr.λf. r (λz. f (cons b z)))) in
      (l h2 d2)

val test_list : List(CBool) → Nat → Nat → Nat =
  let bB=λb.λr. (b cfls r) in
  λl.λn.λm. (l bB ctru n m)

val list : Nat → List(CBool) =
  λk. (k (cons cfls) (cons ctru nil))

val pred : List(CBool) → List(CBool) =
  let gG = λa.λy.λb. (b (cons a (y ctru)) (cons (neg a) (y a))) in
  let dD = λb. nil in
  λl. (l gG dD cfls)

val next : (List(CBool) → Nat) → List(CBool) → Nat =
  λg.λl. (test_list l (s (g l)) (lstore (pred l) g))

val dif : Nat → Nat → Nat =λn.λk. (n next (λx. zero) (list k))

val test : Nat → Nat → CBool → CBool → CBool =λn.λk.λa.λb. (dif n k (λx. a) b)

val init : Nat → Nat → Nat → Nat → CBool =λn.λm.λp.λq. ctru

val iteration : (Nat → Nat → Nat → Nat → CBool) → (Nat → Nat → Nat → Nat → CBool) =
  λg.λn.λm.λk.λp.
        (m (λx.
        n (λx. test n k (test m k (g n m (s k) k) cfls)
          (test m k ctru ((nstore (dif m p) (nstore (dif n p) g)) zero zero))) ctru) cfls)

val inf : Nat → Nat → CBool =λn.λm. (s (s (s ( s (s (s ( s (s n))))))) iteration init n m zero zero)

val good_inf =λn.λm. (inf n m n m)
