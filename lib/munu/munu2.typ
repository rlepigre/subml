(* Type constructor definition. *)
type T(A, B) = [C0 | C1 of A | C2 of B]

(* Type definitions. *)
type Tab = μA μB [C0 | C1 of A | C2 of B]
type TaB = μA νB [C0 | C1 of A | C2 of B]
type TAb = νA μB [C0 | C1 of A | C2 of B]
type TAB = νA νB [C0 | C1 of A | C2 of B]
type Tba = μB μA [C0 | C1 of A | C2 of B]
type TbA = μB νA [C0 | C1 of A | C2 of B]
type TBa = νB μA [C0 | C1 of A | C2 of B]
type TBA = νB νA [C0 | C1 of A | C2 of B]

(* The tests. *)
check Tab ⊂ Tab
check Tab ⊂ TaB
(*
check Tab ⊂ TAb
check Tab ⊂ TAB
check Tab ⊂ Tba
check Tab ⊂ TbA
check Tab ⊂ TBa
check Tab ⊂ TBA
!check TaB ⊂ Tab
check TaB ⊂ TaB
!check TaB ⊂ TAb
check TaB ⊂ TAB
!check TaB ⊂ Tba
!check TaB ⊂ TbA
check TaB ⊂ TBa
check TaB ⊂ TBA
!check TAb ⊂ Tab
!check TAb ⊂ TaB
check TAb ⊂ TAb
check TAb ⊂ TAB
!check TAb ⊂ Tba
!check TAb ⊂ TbA
!check TAb ⊂ TBa
check TAb ⊂ TBA
!check TAB ⊂ Tab
!check TAB ⊂ TaB
!check TAB ⊂ TAb
check TAB ⊂ TAB
!check TAB ⊂ Tba
!check TAB ⊂ TbA
!check TAB ⊂ TBa
check TAB ⊂ TBA
*)