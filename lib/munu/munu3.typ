(* Type constructor definition. *)
type T(A, B, C) = [C0 | C1 of A | C2 of B | C3 of C]

(* Type definitions. *)
type Tabc = μA μB μC [C0 | C1 of A | C2 of B | C3 of C]
type TabC = μA μB νC [C0 | C1 of A | C2 of B | C3 of C]
type TaBc = μA νB μC [C0 | C1 of A | C2 of B | C3 of C]
type TaBC = μA νB νC [C0 | C1 of A | C2 of B | C3 of C]
type TAbc = νA μB μC [C0 | C1 of A | C2 of B | C3 of C]
type TAbC = νA μB νC [C0 | C1 of A | C2 of B | C3 of C]
type TABc = νA νB μC [C0 | C1 of A | C2 of B | C3 of C]
type TABC = νA νB νC [C0 | C1 of A | C2 of B | C3 of C]
type Tacb = μA μC μB [C0 | C1 of A | C2 of B | C3 of C]
type TacB = μA μC νB [C0 | C1 of A | C2 of B | C3 of C]
type TaCb = μA νC μB [C0 | C1 of A | C2 of B | C3 of C]
type TaCB = μA νC νB [C0 | C1 of A | C2 of B | C3 of C]
type TAcb = νA μC μB [C0 | C1 of A | C2 of B | C3 of C]
type TAcB = νA μC νB [C0 | C1 of A | C2 of B | C3 of C]
type TACb = νA νC μB [C0 | C1 of A | C2 of B | C3 of C]
type TACB = νA νC νB [C0 | C1 of A | C2 of B | C3 of C]
type Tbac = μB μA μC [C0 | C1 of A | C2 of B | C3 of C]
type TbaC = μB μA νC [C0 | C1 of A | C2 of B | C3 of C]
type TbAc = μB νA μC [C0 | C1 of A | C2 of B | C3 of C]
type TbAC = μB νA νC [C0 | C1 of A | C2 of B | C3 of C]
type TBac = νB μA μC [C0 | C1 of A | C2 of B | C3 of C]
type TBaC = νB μA νC [C0 | C1 of A | C2 of B | C3 of C]
type TBAc = νB νA μC [C0 | C1 of A | C2 of B | C3 of C]
type TBAC = νB νA νC [C0 | C1 of A | C2 of B | C3 of C]
type Tbca = μB μC μA [C0 | C1 of A | C2 of B | C3 of C]
type TbcA = μB μC νA [C0 | C1 of A | C2 of B | C3 of C]
type TbCa = μB νC μA [C0 | C1 of A | C2 of B | C3 of C]
type TbCA = μB νC νA [C0 | C1 of A | C2 of B | C3 of C]
type TBca = νB μC μA [C0 | C1 of A | C2 of B | C3 of C]
type TBcA = νB μC νA [C0 | C1 of A | C2 of B | C3 of C]
type TBCa = νB νC μA [C0 | C1 of A | C2 of B | C3 of C]
type TBCA = νB νC νA [C0 | C1 of A | C2 of B | C3 of C]
type Tcab = μC μA μB [C0 | C1 of A | C2 of B | C3 of C]
type TcaB = μC μA νB [C0 | C1 of A | C2 of B | C3 of C]
type TcAb = μC νA μB [C0 | C1 of A | C2 of B | C3 of C]
type TcAB = μC νA νB [C0 | C1 of A | C2 of B | C3 of C]
type TCab = νC μA μB [C0 | C1 of A | C2 of B | C3 of C]
type TCaB = νC μA νB [C0 | C1 of A | C2 of B | C3 of C]
type TCAb = νC νA μB [C0 | C1 of A | C2 of B | C3 of C]
type TCAB = νC νA νB [C0 | C1 of A | C2 of B | C3 of C]
type Tcba = μC μB μA [C0 | C1 of A | C2 of B | C3 of C]
type TcbA = μC μB νA [C0 | C1 of A | C2 of B | C3 of C]
type TcBa = μC νB μA [C0 | C1 of A | C2 of B | C3 of C]
type TcBA = μC νB νA [C0 | C1 of A | C2 of B | C3 of C]
type TCba = νC μB μA [C0 | C1 of A | C2 of B | C3 of C]
type TCbA = νC μB νA [C0 | C1 of A | C2 of B | C3 of C]
type TCBa = νC νB μA [C0 | C1 of A | C2 of B | C3 of C]
type TCBA = νC νB νA [C0 | C1 of A | C2 of B | C3 of C]

(* The tests. *)
check Tabc ⊂ Tabc
check Tabc ⊂ TabC
check Tabc ⊂ TaBc
check Tabc ⊂ TaBC
check Tabc ⊂ TAbc
check Tabc ⊂ TAbC
check Tabc ⊂ TABc
check Tabc ⊂ TABC
check Tabc ⊂ Tacb
check Tabc ⊂ TacB
check Tabc ⊂ TaCb
check Tabc ⊂ TaCB
check Tabc ⊂ TAcb
check Tabc ⊂ TAcB
check Tabc ⊂ TACb
check Tabc ⊂ TACB
check Tabc ⊂ Tbac
check Tabc ⊂ TbaC
check Tabc ⊂ TbAc
(*
check Tabc ⊂ TbAC
check Tabc ⊂ TBac
check Tabc ⊂ TBaC
check Tabc ⊂ TBAc
check Tabc ⊂ TBAC
check Tabc ⊂ Tbca
check Tabc ⊂ TbcA
check Tabc ⊂ TbCa
check Tabc ⊂ TbCA
check Tabc ⊂ TBca
check Tabc ⊂ TBcA
check Tabc ⊂ TBCa
check Tabc ⊂ TBCA
check Tabc ⊂ Tcab
check Tabc ⊂ TcaB
check Tabc ⊂ TcAb
check Tabc ⊂ TcAB
check Tabc ⊂ TCab
check Tabc ⊂ TCaB
check Tabc ⊂ TCAb
check Tabc ⊂ TCAB
check Tabc ⊂ Tcba
check Tabc ⊂ TcbA
check Tabc ⊂ TcBa
check Tabc ⊂ TcBA
check Tabc ⊂ TCba
check Tabc ⊂ TCbA
check Tabc ⊂ TCBa
check Tabc ⊂ TCBA
!check TabC ⊂ Tabc
check TabC ⊂ TabC
!check TabC ⊂ TaBc
check TabC ⊂ TaBC
!check TabC ⊂ TAbc
check TabC ⊂ TAbC
!check TabC ⊂ TABc
check TabC ⊂ TABC
!check TabC ⊂ Tacb
!check TabC ⊂ TacB
check TabC ⊂ TaCb
check TabC ⊂ TaCB
!check TabC ⊂ TAcb
!check TabC ⊂ TAcB
check TabC ⊂ TACb
check TabC ⊂ TACB
!check TabC ⊂ Tbac
check TabC ⊂ TbaC
!check TabC ⊂ TbAc
check TabC ⊂ TbAC
!check TabC ⊂ TBac
check TabC ⊂ TBaC
!check TabC ⊂ TBAc
check TabC ⊂ TBAC
!check TabC ⊂ Tbca
!check TabC ⊂ TbcA
check TabC ⊂ TbCa
check TabC ⊂ TbCA
!check TabC ⊂ TBca
!check TabC ⊂ TBcA
check TabC ⊂ TBCa
check TabC ⊂ TBCA
!check TabC ⊂ Tcab
!check TabC ⊂ TcaB
!check TabC ⊂ TcAb
!check TabC ⊂ TcAB
check TabC ⊂ TCab
check TabC ⊂ TCaB
check TabC ⊂ TCAb
check TabC ⊂ TCAB
!check TabC ⊂ Tcba
!check TabC ⊂ TcbA
!check TabC ⊂ TcBa
!check TabC ⊂ TcBA
check TabC ⊂ TCba
check TabC ⊂ TCbA
check TabC ⊂ TCBa
check TabC ⊂ TCBA
!check TaBc ⊂ Tabc
!check TaBc ⊂ TabC
check TaBc ⊂ TaBc
check TaBc ⊂ TaBC
!check TaBc ⊂ TAbc
!check TaBc ⊂ TAbC
check TaBc ⊂ TABc
check TaBc ⊂ TABC
!check TaBc ⊂ Tacb
!check TaBc ⊂ TacB
!check TaBc ⊂ TaCb
check TaBc ⊂ TaCB
!check TaBc ⊂ TAcb
!check TaBc ⊂ TAcB
!check TaBc ⊂ TACb
check TaBc ⊂ TACB
!check TaBc ⊂ Tbac
!check TaBc ⊂ TbaC
!check TaBc ⊂ TbAc
!check TaBc ⊂ TbAC
check TaBc ⊂ TBac
check TaBc ⊂ TBaC
check TaBc ⊂ TBAc
check TaBc ⊂ TBAC
!check TaBc ⊂ Tbca
!check TaBc ⊂ TbcA
!check TaBc ⊂ TbCa
!check TaBc ⊂ TbCA
check TaBc ⊂ TBca
check TaBc ⊂ TBcA
check TaBc ⊂ TBCa
check TaBc ⊂ TBCA
!check TaBc ⊂ Tcab
!check TaBc ⊂ TcaB
!check TaBc ⊂ TcAb
!check TaBc ⊂ TcAB
!check TaBc ⊂ TCab
check TaBc ⊂ TCaB
!check TaBc ⊂ TCAb
check TaBc ⊂ TCAB
!check TaBc ⊂ Tcba
!check TaBc ⊂ TcbA
!check TaBc ⊂ TcBa
!check TaBc ⊂ TcBA
!check TaBc ⊂ TCba
!check TaBc ⊂ TCbA
check TaBc ⊂ TCBa
check TaBc ⊂ TCBA
!check TaBC ⊂ Tabc
!check TaBC ⊂ TabC
!check TaBC ⊂ TaBc
check TaBC ⊂ TaBC
!check TaBC ⊂ TAbc
!check TaBC ⊂ TAbC
!check TaBC ⊂ TABc
check TaBC ⊂ TABC
!check TaBC ⊂ Tacb
!check TaBC ⊂ TacB
!check TaBC ⊂ TaCb
check TaBC ⊂ TaCB
!check TaBC ⊂ TAcb
!check TaBC ⊂ TAcB
!check TaBC ⊂ TACb
check TaBC ⊂ TACB
!check TaBC ⊂ Tbac
!check TaBC ⊂ TbaC
!check TaBC ⊂ TbAc
!check TaBC ⊂ TbAC
!check TaBC ⊂ TBac
check TaBC ⊂ TBaC
!check TaBC ⊂ TBAc
check TaBC ⊂ TBAC
!check TaBC ⊂ Tbca
!check TaBC ⊂ TbcA
!check TaBC ⊂ TbCa
!check TaBC ⊂ TbCA
!check TaBC ⊂ TBca
!check TaBC ⊂ TBcA
check TaBC ⊂ TBCa
check TaBC ⊂ TBCA
!check TaBC ⊂ Tcab
!check TaBC ⊂ TcaB
!check TaBC ⊂ TcAb
!check TaBC ⊂ TcAB
!check TaBC ⊂ TCab
check TaBC ⊂ TCaB
!check TaBC ⊂ TCAb
check TaBC ⊂ TCAB
!check TaBC ⊂ Tcba
!check TaBC ⊂ TcbA
!check TaBC ⊂ TcBa
!check TaBC ⊂ TcBA
!check TaBC ⊂ TCba
!check TaBC ⊂ TCbA
check TaBC ⊂ TCBa
check TaBC ⊂ TCBA
!check TAbc ⊂ Tabc
!check TAbc ⊂ TabC
!check TAbc ⊂ TaBc
!check TAbc ⊂ TaBC
check TAbc ⊂ TAbc
check TAbc ⊂ TAbC
check TAbc ⊂ TABc
check TAbc ⊂ TABC
!check TAbc ⊂ Tacb
!check TAbc ⊂ TacB
!check TAbc ⊂ TaCb
!check TAbc ⊂ TaCB
check TAbc ⊂ TAcb
check TAbc ⊂ TAcB
check TAbc ⊂ TACb
check TAbc ⊂ TACB
!check TAbc ⊂ Tbac
!check TAbc ⊂ TbaC
!check TAbc ⊂ TbAc
!check TAbc ⊂ TbAC
!check TAbc ⊂ TBac
!check TAbc ⊂ TBaC
check TAbc ⊂ TBAc
check TAbc ⊂ TBAC
!check TAbc ⊂ Tbca
!check TAbc ⊂ TbcA
!check TAbc ⊂ TbCa
!check TAbc ⊂ TbCA
!check TAbc ⊂ TBca
!check TAbc ⊂ TBcA
!check TAbc ⊂ TBCa
check TAbc ⊂ TBCA
!check TAbc ⊂ Tcab
!check TAbc ⊂ TcaB
!check TAbc ⊂ TcAb
!check TAbc ⊂ TcAB
!check TAbc ⊂ TCab
!check TAbc ⊂ TCaB
check TAbc ⊂ TCAb
check TAbc ⊂ TCAB
!check TAbc ⊂ Tcba
!check TAbc ⊂ TcbA
!check TAbc ⊂ TcBa
!check TAbc ⊂ TcBA
!check TAbc ⊂ TCba
!check TAbc ⊂ TCbA
!check TAbc ⊂ TCBa
check TAbc ⊂ TCBA
!check TAbC ⊂ Tabc
!check TAbC ⊂ TabC
!check TAbC ⊂ TaBc
!check TAbC ⊂ TaBC
!check TAbC ⊂ TAbc
check TAbC ⊂ TAbC
!check TAbC ⊂ TABc
check TAbC ⊂ TABC
!check TAbC ⊂ Tacb
!check TAbC ⊂ TacB
!check TAbC ⊂ TaCb
!check TAbC ⊂ TaCB
!check TAbC ⊂ TAcb
!check TAbC ⊂ TAcB
check TAbC ⊂ TACb
check TAbC ⊂ TACB
!check TAbC ⊂ Tbac
!check TAbC ⊂ TbaC
!check TAbC ⊂ TbAc
!check TAbC ⊂ TbAC
!check TAbC ⊂ TBac
!check TAbC ⊂ TBaC
!check TAbC ⊂ TBAc
check TAbC ⊂ TBAC
!check TAbC ⊂ Tbca
!check TAbC ⊂ TbcA
!check TAbC ⊂ TbCa
!check TAbC ⊂ TbCA
!check TAbC ⊂ TBca
!check TAbC ⊂ TBcA
!check TAbC ⊂ TBCa
check TAbC ⊂ TBCA
!check TAbC ⊂ Tcab
!check TAbC ⊂ TcaB
!check TAbC ⊂ TcAb
!check TAbC ⊂ TcAB
!check TAbC ⊂ TCab
!check TAbC ⊂ TCaB
check TAbC ⊂ TCAb
check TAbC ⊂ TCAB
!check TAbC ⊂ Tcba
!check TAbC ⊂ TcbA
!check TAbC ⊂ TcBa
!check TAbC ⊂ TcBA
!check TAbC ⊂ TCba
!check TAbC ⊂ TCbA
!check TAbC ⊂ TCBa
check TAbC ⊂ TCBA
!check TABc ⊂ Tabc
!check TABc ⊂ TabC
!check TABc ⊂ TaBc
!check TABc ⊂ TaBC
!check TABc ⊂ TAbc
!check TABc ⊂ TAbC
check TABc ⊂ TABc
check TABc ⊂ TABC
!check TABc ⊂ Tacb
!check TABc ⊂ TacB
!check TABc ⊂ TaCb
!check TABc ⊂ TaCB
!check TABc ⊂ TAcb
!check TABc ⊂ TAcB
!check TABc ⊂ TACb
check TABc ⊂ TACB
!check TABc ⊂ Tbac
!check TABc ⊂ TbaC
!check TABc ⊂ TbAc
!check TABc ⊂ TbAC
!check TABc ⊂ TBac
!check TABc ⊂ TBaC
check TABc ⊂ TBAc
check TABc ⊂ TBAC
!check TABc ⊂ Tbca
!check TABc ⊂ TbcA
!check TABc ⊂ TbCa
!check TABc ⊂ TbCA
!check TABc ⊂ TBca
!check TABc ⊂ TBcA
!check TABc ⊂ TBCa
check TABc ⊂ TBCA
!check TABc ⊂ Tcab
!check TABc ⊂ TcaB
!check TABc ⊂ TcAb
!check TABc ⊂ TcAB
!check TABc ⊂ TCab
!check TABc ⊂ TCaB
!check TABc ⊂ TCAb
check TABc ⊂ TCAB
!check TABc ⊂ Tcba
!check TABc ⊂ TcbA
!check TABc ⊂ TcBa
!check TABc ⊂ TcBA
!check TABc ⊂ TCba
!check TABc ⊂ TCbA
!check TABc ⊂ TCBa
check TABc ⊂ TCBA
!check TABC ⊂ Tabc
!check TABC ⊂ TabC
!check TABC ⊂ TaBc
!check TABC ⊂ TaBC
!check TABC ⊂ TAbc
!check TABC ⊂ TAbC
!check TABC ⊂ TABc
check TABC ⊂ TABC
!check TABC ⊂ Tacb
!check TABC ⊂ TacB
!check TABC ⊂ TaCb
!check TABC ⊂ TaCB
!check TABC ⊂ TAcb
!check TABC ⊂ TAcB
!check TABC ⊂ TACb
check TABC ⊂ TACB
!check TABC ⊂ Tbac
!check TABC ⊂ TbaC
!check TABC ⊂ TbAc
!check TABC ⊂ TbAC
!check TABC ⊂ TBac
!check TABC ⊂ TBaC
!check TABC ⊂ TBAc
check TABC ⊂ TBAC
!check TABC ⊂ Tbca
!check TABC ⊂ TbcA
!check TABC ⊂ TbCa
!check TABC ⊂ TbCA
!check TABC ⊂ TBca
!check TABC ⊂ TBcA
!check TABC ⊂ TBCa
check TABC ⊂ TBCA
!check TABC ⊂ Tcab
!check TABC ⊂ TcaB
!check TABC ⊂ TcAb
!check TABC ⊂ TcAB
!check TABC ⊂ TCab
!check TABC ⊂ TCaB
!check TABC ⊂ TCAb
check TABC ⊂ TCAB
!check TABC ⊂ Tcba
!check TABC ⊂ TcbA
!check TABC ⊂ TcBa
!check TABC ⊂ TcBA
!check TABC ⊂ TCba
!check TABC ⊂ TCbA
!check TABC ⊂ TCBa
check TABC ⊂ TCBA
*)