#Loop by comparing
#   F < F → F → X
#with
#   F = ∀N0 ∀N1 (N0 → (N0 → N0 → N1) → N1)

typed;

let g = λx y. y x x;

let h = g g g;
