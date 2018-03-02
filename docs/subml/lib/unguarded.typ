(* check failure of termination for some unguarder examples *)
type Empty = μX.X

!val rec f : Empty → Empty = fun x → f x

type Full = νX.X

!val rec f : Full → Full = fun x → f x

type S = νX.[ S of X ]

!val rec i : S = S i

!val rec i : {} → S = fun _ → S (i {})
