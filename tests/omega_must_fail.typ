type A = μX [C of (X → X)]

!val delta : A → A = fun x:A → case x:A of C (f:A→A) → f x

type B = νX [C of (X → X)]

val delta : B → B = fun x → case x of C (f:B→B) → f x

!val omega : {} → A = fun _ → delta (C delta)
