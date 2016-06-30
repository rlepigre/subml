(* The error monad: *)
typed;

type Err(K) = ∀X ((K → X) → X → X);

let Error : ∀K Err(K) = λok err.err;
let unit    : ∀K (K → Err(K)) = λn ok err.(ok n);
let bind : ∀K∀K' (Err(K) → (K → Err(K')) → Err(K'))
  = fun n f ↦ n (λx. f x) Error;
let catch : ∀K∀K' (Err(K) → (K → K') → K' → K')
  = fun e f g ↦ e (λx. f x) g;

(* abstract Err; *)