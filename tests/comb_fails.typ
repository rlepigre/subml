(* Typical example of function that cannot be shown terminating by means of
   the size-change principle (tree linearization). *)

type Tree(A) = μX [ Nil | Cons of (A × X × X) ]

(* Type-checks, but termination checker fails. *)
?val rec comb1 : ∀A Tree(A) → Tree(A) = fun x →
  case x of
  | []     → []
  | Cons c →
      (case c.2 of
       | []      → Cons (c.1, [], comb1 c.3)
       | Cons c' → comb1 (Cons (c'.1, c'.2, Cons (c.1, c'.3, c.3))))

(* Type-checks, but termination checker fails. *)
?val rec comb2 : ∀A Tree(A) → Tree(A) = fun x →
  case x of
  | []     → []
  | Cons c →
      (case c.2 of
       | []      → Cons (c.1, [], comb2 c.3)
       | Cons c' → comb2 (Cons (c'.1, c'.3, Cons (c.1, c'.2, c.3))))

(* Type-checks, but termination checker fails. *)
?val rec comb3 : ∀A Tree(A) → Tree(A) = fun x →
  case x of
  | []     → []
  | Cons c →
      (case c.2 of
       | []      → Cons (c.1, [], comb3 c.3)
       | Cons c' → comb3 (Cons (c'.1, c'.2, Cons (c.1, c.3, c'.3))))

(* Type-checks, but termination checker fails. *)
?val rec comb4 : ∀A Tree(A) → Tree(A) = fun x →
  case x of
  | []     → []
  | Cons c →
      (case c.2 of
       | []      → Cons (c.1, [], comb4 c.3)
       | Cons c' → comb4 (Cons (c'.1, c'.3, Cons (c.1, c.3, c'.2))))
