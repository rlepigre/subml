
type N(α) = μα X [ Z | S of X ]
type IN = N(∞)

type F = ∀X X
type N(A) = (A → F)
type NN(A) = N(N(A))
type Peirce = ∀A (N(A) → F) → A

type S(α,A) = να X {} → A × X
type IS(A) = S(∞,A)

type T(A,B) = μX [End of B | Cont of A → X]

val f : ∀A ∀B Peirce → (IS(A) → B) → T(A,B) = fun cc f →
  let A,B such that _ : T(A,B) in
  cc (fun alpha:N(T(A,B)) →
     alpha (End (f (fun _ → cc (fun beta:N(A×IS(A)) →
       let rec aux : ∀α NN(A×S(α,A)) = fun beta →
         alpha (Cont (fun a:A → beta (a, fun _ → cc aux)))
       in
       aux beta)))))
