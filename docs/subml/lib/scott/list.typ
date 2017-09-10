(* List using sums encoded as product *)

type List(A) = μ K ∀X ({ nil : X ; cons : A × K -> X } -> X)

val nil : ∀A List(A)= λx.x.nil

val cons : ∀A (A → List(A) → List(A)) = fun a l x → x.cons (a, l)

type T(A,P) = ∀Y (A × ({ nil : Y → P; cons : Y } → Y → P) → Y → P)
type List'(A) = ∀P ({cons : T(A,P) ; nil : T(A,P) → P } → T(A,P) → P)

val iter_list : ∀A∀P (List(A) → P → (A → P → P) → P) =
  fun l a f →
    let A, P such that f : A → P → P in
    let delta : T(A,P) = fun p x → f p.1 (p.2 { nil = (fun x → a); cons = x } x) in
    l:List'(A) { nil = (fun x → a); cons = delta} delta

val map : ∀A∀B ((A → B) → (List(A) → List(B))) =
  fun f l →
    let A, B such that f : A → B in
    iter_list l nil:List(B) (fun a l → cons (f a) l)


type T(A,P) = ∀Y (A × ({ nil : Y → List(A) → P; cons : Y } → Y → List(A) → P ) → Y → List(A) → P)
type List'(A) = ∀P ({cons : T(A,P) ; nil : T(A,P) → List(A) → P } → T(A,P) → List(A) → P)

val cdr : ∀A (List(A) → List(A)) = fun l → l { nil = nil; cons = (fun l → l.2) }

val rec_list : ∀A∀P (List(A) → P → (List(A) → P → P) → P) =
  fun l a f →
    let A,P such that f : List(A) → P → P in
    let delta : T(A,P) = fun p x l → f l (p.2 { nil = (fun x l → a); cons = x } x (cdr l)) in
    l:List'(A) { nil = (fun x l → a); cons = delta} delta l

type F_List(A,K) = ∀X ({ nil : X ; cons : A × K -> X } -> X)
type T(A,P) = ∀Y (A × ({ nil : Y → P; cons : Y } → Y → P ) → Y → P)
type List'(A) = ∀P ({cons : T(A,P) ; nil : T(A,P) → P } → T(A,P) → P)

val fix_list : ∀A ∀P (∀K (K → P) → F_List(A,K) → P) → List(A) → P =
  fun f n  →
    let A such that n : List(A) in
    let P such that _ : P in
    let nil' : ∀Y (Y → P) =
           fun r → f (fun x → x) (λx.x.nil) in
    let cons' : T(A,P) =
           fun p r → f (fun s → p.2 { nil = nil'; cons = r } r) (fun x → x.cons p) in
    (n:List'(A) {nil = nil' ; cons = cons'}):(T(A,P) → P) cons'
