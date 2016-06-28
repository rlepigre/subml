type F(X) = [ Z | S of X ]

val if_max : ∀o1∀o2 Bool → (μo1 X F(X)) → (μo2 X F(X)) → μmax(o1,o2) X F(X) =
  fun b n m → if b then n else m

val rec maxi : ∀o1∀o2 (μo1 X F(X)) → (μo2 X F(X)) → μmax(o1,o2) X F(X) =
  fun n m →
    case n of
    | Z     → m
    | S[n'] → case m of
              | Z     → n
              | S[m'] → S[maxi n' m']

(* First and second projection with the same type. *)
val fst : ∀o1 ∀o2 (μo1 X F(X)) → (μo2 X F(X)) → (μmax(o1,o2) X F(X)) =
  fun x y ↦ x

val snd : ∀o1 ∀o2 (μo1 X F(X)) → (μo2 X F(X)) → (μmax(o1,o2) X F(X)) =
  fun x y ↦ y
