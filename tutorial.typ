(****************************************************************************)
(*                              SubML Tutorial                              *)
(****************************************************************************)
(*                                                                          *)
(* This page contains a typechecker and interpreter for the SubML language, *)
(* which will be introduced in this tutorial. Like in OCaml or SML, records *)
(* and (polymorphic) variants are provided.                                 *)

type Boolean = [True | False]
type Pair    = {fst : Boolean ; snd : Boolean}

val true      : Boolean = True
val falsetrue : Pair    = {fst = False ; snd = True}

(* The language provides two declaration directives: [type <name> = <type>] *)
(* for naming a type, and [val <name> : <type> = <term>] for defining a new *)
(* value. Note that it is required to provide a type for value declaration. *)
(* Type declarations are only used to define short and convenient names for *)
(* types. Indeed, the following syntax is equivalent for defining the above *)
(* value [falsetrue].                                                       *)

val falsetrue : {fst : [True | False] ; snd : [True | False]} =
  {fst = False ; snd = True}

(* In the system, it is possible to define types with parameters.           *)

type Either(A,B) = [InL of A | InR of B]

val inlBool : Boolean → Either(Boolean, Boolean) = fun b → InL b

(* Note that the arrow symbol [→] denotes the function type. In the editor, *)
(* it can be entered with the character sequence [->], followed by a space. *)
(* In general, unicode characters can be entered using corresponding  LaTex *)
(* macro name ([\to] in the case of [→]). Usual projections for records and *)
(* (shallow) pattern matching are provided.                                 *)

val cond : ∀X.Boolean → X → X → X = fun c t e →
  case c of
  | True  → t
  | False → e

val fst : Pair → Boolean = fun p → p.fst

(* The next (very) important feature of the system is polymorphism. We  use *)
(* the symbol [∀] (entered using [forall], [\forall] or [/\])  to  quantify *)
(* over a type variable.                                                    *)

val id : ∀X.X → X = fun x → x

type Maybe(A) = [Nothing | Just of A]

val fromJust : ∀A.Maybe(A) → A → A = fun m d →
  case m of
  | Nothing → d
  | Just v  → v

(* In the system, types are not implicitly recursive. Inductive  types  and *)
(* coinductive types are defined explicitly using the binders [μ]  and  [ν] *)
(* (entered using [\mu] or [!], and [\nu] or [?] respectively).             *)

type Unary = μN.[Zero | Succ of N]

val zero  : Unary = Zero
val one   : Unary = Succ Zero
val two   : Unary = Succ (Succ Zero)
val three : Unary = Succ (Succ (Succ Zero))

val rec add : Unary → Unary → Unary = fun n m →
  case n of
  | Zero    → m
  | Succ n' → Succ (add n' m)

(* The [Run] button below the editor is used to typecheck its contents. The *)
(* result is then displayed in the log at the bottom.                       *)

eval add three (add two one)
eval (fun x y → x) zero two
eval (fun x y z → x)

(* The command [eval] can be used in the editor to  evaluate  a  term.  The *)
(* obtained value is the displayed in the log. Note than an error is raised *)
(* if the type of the expression cannot be inferred.                        *)

(* A convenient syntax [A1 × ... × AN] is provided for n-ary product types. *)
(* They are encoded into record types with numeric labels from [1] to  [N]. *)
(* The correspondig syntax for tuples is [(a1, ..., aN)].                   *)

val pair : ∀A.∀B.A → B → A × B = fun a b → (a, b)

val fst  : ∀A.∀B.A × B → A = fun p → p.1

(* Subml allows for sized type, i.e. a type with a size parameter. The size *)
(* parameter is given next to the μ or ν and represent the maximum size for *)
(* inductive types and the minimum size for coinductive types.              *)

type L(α,A) = μα X.[ Nil | Cons of A × X ]

val rec map : ∀α.∀A.∀B.(A → B) → L(α,A) → L(α,B) = fun f l →
  case l of
  | Nil        → Nil
  | Cons(a,l') → Cons(f a, map f l')

(* Here L(α,A) is the type of lists of size at most α. Using this type,  we *)
(* can program the classic map function on lists, with the indication  that *)
(* it preserves the size of lists.                                          *)

(* A syntax [[]] can be used for the [Nil] constructor, and [x::l]  can  be *)
(* used for [Cons { hd = x; tl = l; }].                                     *)

type L(α,A) = μα X.[ Nil | Cons of { hd : A ; tl : X } ]

val rec map : ∀α.∀A.∀B.(A → B) → L(α,A) → L(α,B) = fun f l →
  case l of
  | []      → []
  | a :: l' → f a :: map f l'

(* Subml only allows for terminating programs, and it relies on ordinals to *)
(* establish termination. Size informations on functions is thus  essential *)
(* for proving termination.                                                 *)

val rec mapSucc : ∀α.L(α,Unary) → L(α,Unary) = fun l →
  case l of
  | []      → []
  | a :: l' → a :: mapSucc (map (fun x → Succ x) l')

eval mapSucc (Zero::Zero::Zero::[])

(* Size can use +1, +2, ... to indicate variation of sizes.                 *)

val tail : ∀α.∀A.L(α+1,A) → L(α,A) = fun l →
  case l of
  | []     → abort
  | _ :: l → l

(* Remark: one must use abort to have the given type, because de empty list *)
(* is of size one not zero. Without abort, we can only do the following.    *)

val tail : ∀α.∀A.L(α+2,A) → L(α+1,A) = fun l →
  case l of
  | []     → []
  | _ :: l → l

(* Subml also allows local definitions that may be recursive.               *)
val rev : ∀A.L(∞,A) → L(∞,A) =
  let rec aux : ∀A.L(∞,A) → L(∞,A) → L(∞,A) = fun l2 l1 →
    case l1 of
    | []     → l2
    | x::l1' → aux (x::l2) l1'
  in
  let A such that _:L(∞,A) → L(∞,A) in
  aux ([]:L(∞,A))

(* In the above example, we cannot use [[]] because the type-checker  would *)
(* then use the type [[Nil]] and fail. To annotate the program, one can use *)
(* the syntax [let A1, ..., AN such that x:B in ...] to fetch types using a *)
(* pattern matching on the type of variables. On may also use [_] to  match *)
(* against the type of the current term. This construct can also be used to *)
(* fetch size annotation by pattern matching.                               *)

(* Subml has coinductive types using ν instead of μ. We can also mix them.  *)

type Bits(α) = να X.{} → [Zero of X | One of X]

val rec bitneg : ∀α.Bits(α) → Bits(α) = fun s _ →
  case s {} of
  | Zero s' → One  (bitneg s')
  | One  s' → Zero (bitneg s')

(* Bits represents the type of an infinite sequence of bits (Zero of One).  *)
(* The size α, denotes a minimum number of bits that must be present.       *)

type Real = νX.μY.{} → [Zero of X | One of Y ]

check Real ⊂ Bits(∞)

(* The type Real is a subtype of Bits(∞) where ∞ represents a large enough  *)
(* size to ensure that we reach a fixpoint (Bits(∞+1) = Bits(∞)). This type *)
(* is not very useful in practice. However if we all positive and negative  *)
(* Ones, we can get quite far (see lib/real.txp).                           *)

(* Functions from SubML's standard library can be loaded  using  [include]. *)
(* They are made available immediatly in the scope. Standard library  files *)
(* include [lib/nat.typ], [lib/list.typ], [lib/set.typ]. A complete list of *)
(* file is given on the right of the page.                                  *)

include "list.typ"

val l : List(Boolean) = cons True (cons False nil)

val l2 = hd l
eval l2
eval tl l
