(* The prelude contains common functions and types. It is automatically loaded
   by SubML, without the need for an explicit “include”. This behaviour can be
   alterd using the “--no-prelude” command-line option. *)

val id  : ∀X X → X        = fun x → x
val fst : ∀X ∀Y X → Y → X = fun x y → x
val snd : ∀X ∀Y X → Y → Y = fun x y → y

val compose : ∀X ∀Y ∀Z (Y → Z) → (X → Y) → X → Z = fun f g x → f (g x)

(* Standard booleans and related functions. *)

type Bool = [Tru | Fls]

val tru : Bool = Tru
val fls : Bool = Fls

val cond : ∀X Bool → X → X → X = fun c t e →
  case c of
  | Tru → t
  | Fls → e

(* NOTE: equivalent to the “if ... then ... else” syntax. *)

val neg : Bool → Bool = fun a →
  if a then fls else tru

val or : Bool → Bool → Bool = fun a b →
  if a then tru else b

val and : Bool → Bool → Bool = fun a b →
  if a then b else fls

(* Standard “option” type and related functions. *)

type Option(A) = [None | Some of A]

val map_option : ∀X ∀Y (X → Y) → Option(X) → Option(Y) = fun f o →
  case o of
  | None   → None
  | Some e → Some(f e)

val from_option : ∀X Option(X) → X → X = fun o d →
  case o of
  | None   → d
  | Some e → e

(* Monadic operations for the “option” type. *)

val return_option : ∀X X → Option(X) = fun x ->
  Some(x)

val bind_option : ∀X ∀Y (X → Option(Y)) → Option(X) → Option(Y) = fun f o →
  case o of
  | None   → None
  | Some e → f e

(* Standard “either” (binary disjoint sum) type and related functions. *)

type Either(A,B) = [InL of A | InR of B]

val from_either : ∀X ∀Y ∀Z (X → Z) → (Y → Z) → Either(X,Y) → Z = fun f g e →
  case e of
  | InL l → f l
  | InR r → g r

(* Standard return type for comparing functions. *)

type Cmp = [Ls | Eq | Gt]
