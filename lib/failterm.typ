type T = μX [ L | N of X * X ]

?val rec peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne (N(N(l,rl),rr)))

?val rec 2 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne (N(N(l,rl),rr)))

?val rec 3 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne (N(N(l,rl),rr)))

?val rec 4 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne (N(N(l,rl),rr)))

(* NOTE: kept because was looping in the previous version of subml *)

!val rec 3 peigne : T → T = fun t → (* still loops with 4 !*)
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne N(N(l,rl),rr)) (*<- here two arguments*)
