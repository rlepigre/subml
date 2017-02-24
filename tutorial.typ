(****************************************************************************)
(*                              SubML Tutorial                              *)
(****************************************************************************)
(*                                                                          *)
(* This tutorial introduce the SubML language. Like in OCaml or SML,        *)
(* records and (polymorphic) variants are provided.                         *)

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

val cond : ∀X Boolean → X → X → X = fun c t e →
  case c of
  | True  → t
  | False → e

val fst : Pair → Boolean = fun p → p.fst

(* The next (very) important feature of the system is polymorphism. We  use *)
(* the symbol [∀] (entered using [forall], [\forall] or [/\])  to  quantify *)
(* over a type variable.                                                    *)

type Maybe(A) = [Nothing | Just of A]
val fromJust : ∀A Maybe(A) → A → A = fun m d →
  case m of
  | Nothing → d
  | Just v  → v

val id : ∀X X → X = fun x → x

(* In the system, types are not implicitly recursive. Inductive  types  and *)
(* coinductive types are defined explicitly using the binders [μ]  and  [ν] *)
(* (entered using [\mu] or [!], and [\nu] or [?] respectively).             *)

type Unary = μN [Zero | Succ of N]

val zero  : Unary = Zero
val one   : Unary = Succ Zero
val two   : Unary = Succ (Succ Zero)
val three : Unary = Succ (Succ (Succ Zero))

val rec add : Unary → Unary → Unary = fun n m →
  case n of
  | Zero    → m
  | Succ n' → Succ (add n' m)

(* The buttons [Load] below the editor is used to typecheck the contents of *)
(* this editor. The result is then displayed in the log at the bottom.      *)

eval add three (add two one)
eval (fun x y → x) zero two
eval (fun x y z → x)

(* The command [eval] can be used in the editor to  evaluate  a  term.  The *)
(* obtained value is the displayed in the log. Note than an error is raised *)
(* if the type of the expression cannot be inferred.                        *)

val idCurry : ∀X X → X = fun x → x

(* In the system, type annotations are sometimes to help the  type-checker. *)
(* Type indications can be given by the used on function arguments  and  on *)
(* subterms. In terms corresponding to polymorphic types, type abstractions *)
(* can be used using the symbol [Λ] (obtained using [\Lambda]). The name of *)
(* the bound type variables should correspond exactly to the  name  of  the *)
(* corresponding variable in the type.                                      *)

(* A syntactic sugar is provided for tuples, using A1 × ... × AN for types  *)
(* and (a1,...,aN) for values. Tuples are just record with numeric labels   *)
(* from 1 to N.                                                             *)

val p : ∀A ∀B A → B → A × B = fun a b → (a, b)

(* Subml allows for sized type, i.e. a type with a size parameter. The size *)
(* parameter is given next to the μ or ν and represent the maximum size for *)
(* inductive types and the minimum size for coinductive types.              *)

type L(α,A) = μα X [ Nil | Cons of A × X ]

val rec map : ∀α ∀A ∀B (A → B) → L(α,A) → L(α,B) = fun f l →
  case l of
  | Nil        → Nil
  | Cons(a,l') → Cons(f a, map f l')

(* Here L(α,A) is the type of lists of size at most α. Using this type, we  *)
(* can program the classic map function on lists, with the indication that  *)
(* it preserves the size of lists.                                          *)

(* A syntactic sugar is provided for lists: [] represents Nil and x::l      *)
(* denotes Cons { hd = x; tl = l; }. This gives the following for lists     *)

type L(α,A) = μα X [ Nil | Cons of { hd : A ; tl : X } ]

val rec map : ∀α ∀A ∀B (A → B) → L(α,A) → L(α,B) = fun f l →
  case l of
  | []      → []
  | a :: l' → f a :: map f l'

(* Subml only allows for terminating programs. The notion of size is this   *)
(* used to establish termination and size information in function are often *)
(* essential to prove termination.                                          *)

val rec mapSucc : ∀α L(α,Unary) → L(α,Unary) = fun l →
  case l of
  | []      → []
  | a :: l' → a :: mapSucc (map (fun x → Succ x) l')

eval mapSucc (Zero::Zero::Zero::[])

(* Size can use +1, +2, ... to indicate variation of sizes.                 *)

val tail : ∀α∀A L(α+1,A) → L(α,A) = fun l →
  case l of
  | []     → abort
  | _ :: l → l

(* Remark: one must use abort to have the given type, because de empty list *)
(* is of size one not zero. Without abort, we can only do the following.    *)

val tail : ∀α∀A L(α+2,A) → L(α+1,A) = fun l →
  case l of
  | []     → []
  | _ :: l → l

(* Subml also allows for local definitions (recursive or not)               *)
val rev : ∀A L(∞,A) → L(∞,A) =
  let rec aux : ∀A L(∞,A) → L(∞,A) → L(∞,A) = fun l2 l1 →
    case l1 of
    | []     → l2
    | x::l1' → aux (x::l2) l1'
  in
  let A such that _:L(∞,A) → L(∞,A) in
  aux ([]:L(∞,A))

(* In this example, if in the last line, we use '[]', Subml uses the type   *)
(* [Nil] and typing fails. To give the necessary typing annotation, one can *)
(* use 'let A1,...,AN such that x:B in ...' This allows to fetch some types *)
(* by pattern matching on the type of a variable. On may use '_' to pattern *)
(* match agains the type of the current term. This construct can also be    *)
(* used to fetch size annotation by pattern matching.                       *)

(* Subml has coinductive types using ν instead of μ. We can also mix them.  *)

type Bits(α) = να X {} → [Zero of X | One of X]

val rec bitneg : ∀α Bits(α) → Bits(α) = fun s _ →
  case s {} of
  | Zero s' → One  (bitneg s')
  | One  s' → Zero (bitneg s')

(* Bits represents the type of an infinite sequence of bits (Zero of One).  *)
(* The size α, denotes a minimum number of bits that must be present.       *)

type Real = νX μY {} → [Zero of X | One of Y ]

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
