(* The error monad: *)
type Err(K) = ∀X ((K → X) → X → X)

val error : ∀K Err(K) = λok err.err
val unit    : ∀K (K → Err(K)) = λn ok err.(ok n)
val bind : ∀K∀K' (Err(K) → (K → Err(K')) → Err(K'))
  = fun n f → n (λx. f x) error
val catch : ∀K∀K' (Err(K) → (K → K') → K' → K')
  = fun e f g → e (λx. f x) g

val printErr : ∀K (K → {}) → Err(K) → {}
  = fun pr x → x (fun x _ → pr x) (fun _ → print("Error\n")) {}
