(* Typical example of function that cannot be shown terminating by means of
   the size-change principle (normalisation of binary decision diagrams). *)

type BDD(A)  = μX.[ Var of A | If of {c : X; t : X; f : X}]

(* Type-checks, but termination checker fails. *)
?val rec norm : ∀A.BDD(A) → BDD(A) = fun t →
  case t of
  | Var v → Var v
  | If c  →
      (case c.c of
       | Var v → If {c = Var v; t = norm c.t; f = norm c.f}
       | If c' → norm (If { c = c'.c
                          ; t = If {c = c'.t; t = c.t; f = c.f}
                          ; f = If {c = c'.f; t = c.t; f = c.f}}))
