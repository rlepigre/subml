type F(X) = [ Z | S of {} → X ]

(* a subtelty here: put mu after arrow type,
   so SN(0) is a function *)
type SN(α) = {} → μα X.F(X)
type N = SN(∞)

val rec idt : N → N = fun n _ →
  case n {} of
  | Z   → Z
  | S p → S(idt p)

(* size preserving identity *)
val rec idt2 : ∀α.SN(α) → SN(α) = fun n _ →
  case n {} of
  | Z   → Z
  | S p → S(idt2 p)

(* a bad version (for perfomance) *)
val rec idt3 : ∀α.SN(α) → SN(α) = fun n →
  case n {} of
  | Z   → fun _ → Z
  | S p → fun _ → S(idt3 p)

val rec add : N → N → N = fun n m →
  case n {} of
  | Z   → m
  | S p → fun _ → S (add p m)
