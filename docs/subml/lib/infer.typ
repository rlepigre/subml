
?val rec[1] id = fun o → case o of
  | Z → Z
  | S x → S (id x)

val rec id = fun o → case o of
  | Z → Z
  | S x → S (id x)

val rec[2] bad_add = fun n m → case n of
  | Z → m (* m is inferred type type μX [ S of X ] *)
  | S x → S (bad_add x m)

val rec[2] add = fun n m → case n of
  | Z → (case m of Z → Z | S _ → m) (* fixes above *)
  | S x → S (add x m)

(* FIXME: does not work *)
?val rec[2] mul = fun n m → case n of
  | Z → Z
  | S x → add (mul x m) m

(* but works if cases are inverted *)
val rec[2] mul = fun n m → case n of
  | S x → add (mul x m) m
  | Z → Z
