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
(*
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
check not TabC ⊂ Tabc
check TabC ⊂ TabC
check not TabC ⊂ TaBc
check TabC ⊂ TaBC
check not TabC ⊂ TAbc
check TabC ⊂ TAbC
check not TabC ⊂ TABc
check TabC ⊂ TABC
check not TabC ⊂ Tacb
check not TabC ⊂ TacB
check TabC ⊂ TaCb
check TabC ⊂ TaCB
check not TabC ⊂ TAcb
check not TabC ⊂ TAcB
check TabC ⊂ TACb
check TabC ⊂ TACB
check not TabC ⊂ Tbac
check TabC ⊂ TbaC
check not TabC ⊂ TbAc
check TabC ⊂ TbAC
check not TabC ⊂ TBac
check TabC ⊂ TBaC
check not TabC ⊂ TBAc
check TabC ⊂ TBAC
check not TabC ⊂ Tbca
check not TabC ⊂ TbcA
check TabC ⊂ TbCa
check TabC ⊂ TbCA
check not TabC ⊂ TBca
check not TabC ⊂ TBcA
check TabC ⊂ TBCa
check TabC ⊂ TBCA
check not TabC ⊂ Tcab
check not TabC ⊂ TcaB
check not TabC ⊂ TcAb
check not TabC ⊂ TcAB
check TabC ⊂ TCab
check TabC ⊂ TCaB
check TabC ⊂ TCAb
check TabC ⊂ TCAB
check not TabC ⊂ Tcba
check not TabC ⊂ TcbA
check not TabC ⊂ TcBa
check not TabC ⊂ TcBA
check TabC ⊂ TCba
check TabC ⊂ TCbA
check TabC ⊂ TCBa
check TabC ⊂ TCBA
check not TaBc ⊂ Tabc
check not TaBc ⊂ TabC
check TaBc ⊂ TaBc
check TaBc ⊂ TaBC
check not TaBc ⊂ TAbc
check not TaBc ⊂ TAbC
check TaBc ⊂ TABc
check TaBc ⊂ TABC
check not TaBc ⊂ Tacb
check not TaBc ⊂ TacB
check not TaBc ⊂ TaCb
check TaBc ⊂ TaCB
check not TaBc ⊂ TAcb
check not TaBc ⊂ TAcB
check not TaBc ⊂ TACb
check TaBc ⊂ TACB
check not TaBc ⊂ Tbac
check not TaBc ⊂ TbaC
check not TaBc ⊂ TbAc
check not TaBc ⊂ TbAC*)
check TaBc ⊂ TBac
(*
check TaBc ⊂ TBaC
check TaBc ⊂ TBAc
check TaBc ⊂ TBAC
check not TaBc ⊂ Tbca
check not TaBc ⊂ TbcA
check not TaBc ⊂ TbCa
check not TaBc ⊂ TbCA
check TaBc ⊂ TBca
check TaBc ⊂ TBcA
check TaBc ⊂ TBCa
check TaBc ⊂ TBCA
check not TaBc ⊂ Tcab
check not TaBc ⊂ TcaB
check not TaBc ⊂ TcAb
check not TaBc ⊂ TcAB
check not TaBc ⊂ TCab
check TaBc ⊂ TCaB
check not TaBc ⊂ TCAb
check TaBc ⊂ TCAB
check not TaBc ⊂ Tcba
check not TaBc ⊂ TcbA
check not TaBc ⊂ TcBa
check not TaBc ⊂ TcBA
check not TaBc ⊂ TCba
check not TaBc ⊂ TCbA
check TaBc ⊂ TCBa
check TaBc ⊂ TCBA
check not TaBC ⊂ Tabc
check not TaBC ⊂ TabC
check not TaBC ⊂ TaBc
check TaBC ⊂ TaBC
check not TaBC ⊂ TAbc
check not TaBC ⊂ TAbC
check not TaBC ⊂ TABc
check TaBC ⊂ TABC
check not TaBC ⊂ Tacb
check not TaBC ⊂ TacB
check not TaBC ⊂ TaCb
check TaBC ⊂ TaCB
check not TaBC ⊂ TAcb
check not TaBC ⊂ TAcB
check not TaBC ⊂ TACb
check TaBC ⊂ TACB
check not TaBC ⊂ Tbac
check not TaBC ⊂ TbaC
check not TaBC ⊂ TbAc
check not TaBC ⊂ TbAC
check not TaBC ⊂ TBac
check TaBC ⊂ TBaC
check not TaBC ⊂ TBAc
check TaBC ⊂ TBAC
check not TaBC ⊂ Tbca
check not TaBC ⊂ TbcA
check not TaBC ⊂ TbCa
check not TaBC ⊂ TbCA
check not TaBC ⊂ TBca
check not TaBC ⊂ TBcA
check TaBC ⊂ TBCa
check TaBC ⊂ TBCA
check not TaBC ⊂ Tcab
check not TaBC ⊂ TcaB
check not TaBC ⊂ TcAb
check not TaBC ⊂ TcAB
check not TaBC ⊂ TCab
check TaBC ⊂ TCaB
check not TaBC ⊂ TCAb
check TaBC ⊂ TCAB
check not TaBC ⊂ Tcba
check not TaBC ⊂ TcbA
check not TaBC ⊂ TcBa
check not TaBC ⊂ TcBA
check not TaBC ⊂ TCba
check not TaBC ⊂ TCbA
check TaBC ⊂ TCBa
check TaBC ⊂ TCBA
check not TAbc ⊂ Tabc
check not TAbc ⊂ TabC
check not TAbc ⊂ TaBc
check not TAbc ⊂ TaBC
check TAbc ⊂ TAbc
check TAbc ⊂ TAbC
check TAbc ⊂ TABc
check TAbc ⊂ TABC
check not TAbc ⊂ Tacb
check not TAbc ⊂ TacB
check not TAbc ⊂ TaCb
check not TAbc ⊂ TaCB
check TAbc ⊂ TAcb
check TAbc ⊂ TAcB
check TAbc ⊂ TACb
check TAbc ⊂ TACB
check not TAbc ⊂ Tbac
check not TAbc ⊂ TbaC
check not TAbc ⊂ TbAc
check not TAbc ⊂ TbAC
check not TAbc ⊂ TBac
check not TAbc ⊂ TBaC
check TAbc ⊂ TBAc
check TAbc ⊂ TBAC
check not TAbc ⊂ Tbca
check not TAbc ⊂ TbcA
check not TAbc ⊂ TbCa
check not TAbc ⊂ TbCA
check not TAbc ⊂ TBca
check not TAbc ⊂ TBcA
check not TAbc ⊂ TBCa
check TAbc ⊂ TBCA
check not TAbc ⊂ Tcab
check not TAbc ⊂ TcaB
check not TAbc ⊂ TcAb
check not TAbc ⊂ TcAB
check not TAbc ⊂ TCab
check not TAbc ⊂ TCaB
check TAbc ⊂ TCAb
check TAbc ⊂ TCAB
check not TAbc ⊂ Tcba
check not TAbc ⊂ TcbA
check not TAbc ⊂ TcBa
check not TAbc ⊂ TcBA
check not TAbc ⊂ TCba
check not TAbc ⊂ TCbA
check not TAbc ⊂ TCBa
check TAbc ⊂ TCBA
check not TAbC ⊂ Tabc
check not TAbC ⊂ TabC
check not TAbC ⊂ TaBc
check not TAbC ⊂ TaBC
check not TAbC ⊂ TAbc
check TAbC ⊂ TAbC
check not TAbC ⊂ TABc
check TAbC ⊂ TABC
check not TAbC ⊂ Tacb
check not TAbC ⊂ TacB
check not TAbC ⊂ TaCb
check not TAbC ⊂ TaCB
check not TAbC ⊂ TAcb
check not TAbC ⊂ TAcB
check TAbC ⊂ TACb
check TAbC ⊂ TACB
check not TAbC ⊂ Tbac
check not TAbC ⊂ TbaC
check not TAbC ⊂ TbAc
check not TAbC ⊂ TbAC
check not TAbC ⊂ TBac
check not TAbC ⊂ TBaC
check not TAbC ⊂ TBAc
check TAbC ⊂ TBAC
check not TAbC ⊂ Tbca
check not TAbC ⊂ TbcA
check not TAbC ⊂ TbCa
check not TAbC ⊂ TbCA
check not TAbC ⊂ TBca
check not TAbC ⊂ TBcA
check not TAbC ⊂ TBCa
check TAbC ⊂ TBCA
check not TAbC ⊂ Tcab
check not TAbC ⊂ TcaB
check not TAbC ⊂ TcAb
check not TAbC ⊂ TcAB
check not TAbC ⊂ TCab
check not TAbC ⊂ TCaB
check TAbC ⊂ TCAb
check TAbC ⊂ TCAB
check not TAbC ⊂ Tcba
check not TAbC ⊂ TcbA
check not TAbC ⊂ TcBa
check not TAbC ⊂ TcBA
check not TAbC ⊂ TCba
check not TAbC ⊂ TCbA
check not TAbC ⊂ TCBa
check TAbC ⊂ TCBA
check not TABc ⊂ Tabc
check not TABc ⊂ TabC
check not TABc ⊂ TaBc
check not TABc ⊂ TaBC
check not TABc ⊂ TAbc
check not TABc ⊂ TAbC
check TABc ⊂ TABc
check TABc ⊂ TABC
check not TABc ⊂ Tacb
check not TABc ⊂ TacB
check not TABc ⊂ TaCb
check not TABc ⊂ TaCB
check not TABc ⊂ TAcb
check not TABc ⊂ TAcB
check not TABc ⊂ TACb
check TABc ⊂ TACB
check not TABc ⊂ Tbac
check not TABc ⊂ TbaC
check not TABc ⊂ TbAc
check not TABc ⊂ TbAC
check not TABc ⊂ TBac
check not TABc ⊂ TBaC
check TABc ⊂ TBAc
check TABc ⊂ TBAC
check not TABc ⊂ Tbca
check not TABc ⊂ TbcA
check not TABc ⊂ TbCa
check not TABc ⊂ TbCA
check not TABc ⊂ TBca
check not TABc ⊂ TBcA
check not TABc ⊂ TBCa
check TABc ⊂ TBCA
check not TABc ⊂ Tcab
check not TABc ⊂ TcaB
check not TABc ⊂ TcAb
check not TABc ⊂ TcAB
check not TABc ⊂ TCab
check not TABc ⊂ TCaB
check not TABc ⊂ TCAb
check TABc ⊂ TCAB
check not TABc ⊂ Tcba
check not TABc ⊂ TcbA
check not TABc ⊂ TcBa
check not TABc ⊂ TcBA
check not TABc ⊂ TCba
check not TABc ⊂ TCbA
check not TABc ⊂ TCBa
check TABc ⊂ TCBA
check not TABC ⊂ Tabc
check not TABC ⊂ TabC
check not TABC ⊂ TaBc
check not TABC ⊂ TaBC
check not TABC ⊂ TAbc
check not TABC ⊂ TAbC
check not TABC ⊂ TABc
check TABC ⊂ TABC
check not TABC ⊂ Tacb
check not TABC ⊂ TacB
check not TABC ⊂ TaCb
check not TABC ⊂ TaCB
check not TABC ⊂ TAcb
check not TABC ⊂ TAcB
check not TABC ⊂ TACb
check TABC ⊂ TACB
check not TABC ⊂ Tbac
check not TABC ⊂ TbaC
check not TABC ⊂ TbAc
check not TABC ⊂ TbAC
check not TABC ⊂ TBac
check not TABC ⊂ TBaC
check not TABC ⊂ TBAc
check TABC ⊂ TBAC
check not TABC ⊂ Tbca
check not TABC ⊂ TbcA
check not TABC ⊂ TbCa
check not TABC ⊂ TbCA
check not TABC ⊂ TBca
check not TABC ⊂ TBcA
check not TABC ⊂ TBCa
check TABC ⊂ TBCA
check not TABC ⊂ Tcab
check not TABC ⊂ TcaB
check not TABC ⊂ TcAb
check not TABC ⊂ TcAB
check not TABC ⊂ TCab
check not TABC ⊂ TCaB
check not TABC ⊂ TCAb
check TABC ⊂ TCAB
check not TABC ⊂ Tcba
check not TABC ⊂ TcbA
check not TABC ⊂ TcBa
check not TABC ⊂ TcBA
check not TABC ⊂ TCba
check not TABC ⊂ TCbA
check not TABC ⊂ TCBa
check TABC ⊂ TCBA
*)