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

(* In the system, it is possible to define types with parameters.  However, *)
(* they should be provided with all their arguments when used in a value.   *)

type Either(A,B) = [InL of A | InR of B]
val inlBool : Boolean → Either(Boolean, Boolean) = fun b ↦ InL b

(* Note that the arrow symbol [→] denotes the function type. In the editor, *)
(* it can be entered with the character sequence [->], followed by a space. *)
(* In general, unicode characters can be entered using corresponding  LaTex *)
(* macro name ([\to] in the case of [→]). The symbol [↦] is obtained  using *)
(* [\mapsto]. It is used to separate the arguments and the body in function *)
(* definitions. Usual record projections and (shallow) pattern matching are *)
(* provided.                                                                *)

val cond : ∀X Boolean → X → X → X = fun c t e ↦
  case c of
  | True  → t
  | False → e

val fst : Pair → Boolean = fun p → p.fst

(* The next (very) important feature of the system is polymorphism. We  use *)
(* the symbol [∀] (entered using [forall], [\forall] or [/\])  to  quantify *)
(* over a type variable.                                                    *)

type Maybe(A) = [Nothing | Just of A]
val fromJust : ∀A Maybe(A) → A → A = fun m d ↦
  case m of
  | Nothing → d
  | Just v  → v

val id : ∀X X → X = fun x ↦ x

(* In the system, types are not implicitly recursive. Inductive  types  and *)
(* coinductive types are defined explicitly using the binders [μ]  and  [ν] *)
(* (entered using [\mu] or [!], and [\nu] or [?] respectively).             *)

type Unary = μN [Zero | Succ of N]

val zero  : Unary = Zero
val one   : Unary = Succ Zero
val two   : Unary = Succ (Succ Zero)
val three : Unary = Succ (Succ (Succ Zero))

val rec add : Unary → Unary → Unary = fun n m ↦
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

val idCurry : ∀X X → X = ΛX fun (x : X) ↦ (x : X)

(* In the system, type annotations are sometimes to help the  type-checker. *)
(* Type indications can be given by the used on function arguments  and  on *)
(* subterms. In terms corresponding to polymorphic types, type abstractions *)
(* can be used using the symbol [Λ] (obtained using [\Lambda]). The name of *)
(* the bound type variables should correspond exactly to the  name  of  the *)
(* corresponding variable in the type.                                      *)

include "lib/list.typ"

val l : List(Boolean) = cons True (cons False nil)

eval hd l
eval tl l

(* Functions from SubML's standard library can be loaded  using  [include]. *)
(* They are made available immediatly in the scope. Standard library  files *)
(* include [lib/nat.typ], [lib/list.typ], [lib/set.typ]. A complete list of *)
(* file is given on the right of the page.                                  *)
