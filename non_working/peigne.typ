
type Tree(A) = μX [ Nil | Cons of (A × X × X) ]

val rec peigne : ∀A Tree(A) → Tree(A) = fun x ↦
  case x of
  | [] → []
  | Cons[c] →
    case c.2 of
    | [] → Cons[(c.1,[],peigne c.3)]
    | Cons[c'] → peigne Cons[(c'.1,c'.2,Cons[(c.1,c'.3,c.3)])]

val rec peigne2 : ∀A Tree(A) → Tree(A) = fun x ↦
  case x of
  | [] → []
  | Cons[c] →
    case c.2 of
    | [] → Cons[(c.1,[],peigne2 c.3)]
    | Cons[c'] → peigne2 Cons[(c'.1,c'.3,Cons[(c.1,c'.2,c.3)])]

val rec peigne3 : ∀A Tree(A) → Tree(A) = fun x ↦
  case x of
  | [] → []
  | Cons[c] →
    case c.2 of
    | [] → Cons[(c.1,[],peigne3 c.3)]
    | Cons[c'] → peigne3 Cons[(c'.1,c'.2,Cons[(c.1,c.3,c'.3)])]

val rec peigne4 : ∀A Tree(A) → Tree(A) = fun x ↦
  case x of
  | [] → []
  | Cons[c] →
    case c.2 of
    | [] → Cons[(c.1,[],peigne4 c.3)]
    | Cons[c'] → peigne4 Cons[(c'.1,c'.3,Cons[(c.1,c.3,c'.2)])]

type Bdd(A)  = μX [ Var of A | If of { c: X; t: X; f: X }]

val rec norm : ∀A Bdd(A) → Bdd(A) = fun t ↦
  case t of
  | Var[v] → Var[v]
  | If[c]  →
    case c.c of
    | Var[v] → If[{ c = Var[v]; t = norm c.t; f = norm c.f}]
    | If[c'] → norm If[{ c = c'.c; t = If[{ c = c'.t; t = c.t; f = c.f}]
                                 ; f = If[{ c = c'.f; t = c.t; f = c.f}] }]
