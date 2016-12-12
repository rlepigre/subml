type T = μX [ L | N of X * X ]

?val rec peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne N(N(l,rl),rr))


?val rec 2 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne N(N(l,rl),rr))

?val rec 3 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne N(N(l,rl),rr))

(* FIXME: make subml loops
?val rec 4 peigne : T → T = fun t →
  case t of
  | L → L
  | N(l,r) →
    (case r of
    | L → N(peigne l,L)
    | N(rl,rr) →
       peigne N(N(l,rl),rr))
*)