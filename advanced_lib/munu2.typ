type H(X) = ∀Y (X → Y) → Y
(* Type constructor definition. *)
type T(A, B) = [C0 | C1 of H(A) | C2 of H(B)]

(* Type definitions. *)
type Tab = μA μB [C0 | C1 of H(A) | C2 of H(B)]
type TaB = μA νB [C0 | C1 of H(A) | C2 of H(B)]
type TAb = νA μB [C0 | C1 of H(A) | C2 of H(B)]
type TAB = νA νB [C0 | C1 of H(A) | C2 of H(B)]
type Tba = μB μA [C0 | C1 of H(A) | C2 of H(B)]
type TbA = μB νA [C0 | C1 of H(A) | C2 of H(B)]
type TBa = νB μA [C0 | C1 of H(A) | C2 of H(B)]
type TBA = νB νA [C0 | C1 of H(A) | C2 of H(B)]

(* The tests. *)
check Tab ⊂ Tab
check Tab ⊂ TaB
check Tab ⊂ TAb
check Tab ⊂ TAB
check Tab ⊂ Tba
check Tab ⊂ TbA
check Tab ⊂ TBa
check Tab ⊂ TBA
check not TaB ⊂ Tab
check TaB ⊂ TaB
check not TaB ⊂ TAb
check TaB ⊂ TAB
check not TaB ⊂ Tba
check not TaB ⊂ TbA
check TaB ⊂ TBa
check TaB ⊂ TBA
check not TAb ⊂ Tab
check not TAb ⊂ TaB
check TAb ⊂ TAb
check TAb ⊂ TAB
check not TAb ⊂ Tba
check not TAb ⊂ TbA
check not TAb ⊂ TBa
check TAb ⊂ TBA
check not TAB ⊂ Tab
check not TAB ⊂ TaB
check not TAB ⊂ TAb
check TAB ⊂ TAB
check not TAB ⊂ Tba
check not TAB ⊂ TbA
check not TAB ⊂ TBa
check TAB ⊂ TBA
