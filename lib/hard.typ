(* A (useless) function that does not pass the semi-continuous condition
   but that is terminating and accepted *)

(* nat and addition *)
type SN(α) = μα X.[Z | S of X]
type N = SN(∞)

val rec add : N → N → N = fun n m →
  case n of
  | Z   → m
  | S x → S(add x m)

(* The type ((SN(α) → Nat) → Nat) → Nat is not semicontinuous in α,
   and still this function is accepted *)
val rec f : ∀α.((SN(α) → N) → N) → N =
  fun x → x (fun n →
    case n of
    | Z   → (Z:N)
    | S p → (f (fun g → x (fun q → add q (g p)))))

(* checking subtyping *)
val f' : ((N → N) → N) → N = f

(* Same function with type annotation *)
val rec f1 : ∀α.((SN(α) → N) → N) → N =
  let α such that _ : ((SN(α) → N) → N) → N in
  fun x → x (fun n →
    case (n:SN(α)) of
    | Z   → (Z:N)
    | S p → (f1 (fun g → x (fun q → add q (g p)))))

(* Type annotation are reuired because the default decoration
   is not ∀α.((SN(α) → N) → N) → N *)
?val rec f2 : ((N → N) → N) → N =
  fun x → x (fun n →
    case n of
    | Z   → (Z:N)
    | S p → (f2 (fun g → x (fun q → add q (g p)))))
