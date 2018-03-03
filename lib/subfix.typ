type T1 = μX.νY.[ Z | A of X | B of Y]
type T2 = νY.μX.[ Z | A of X | B of Y]

check T1 ⊆ T2
!check T2 ⊆ T1

type TxYz = μX.νY.μZ.[ Z | A of X | B of Y | C of Z]
type TxyZ = μX.μY.νZ.[ Z | A of X | B of Y | C of Z]
type TYxz = νY.μX.μZ.[ Z | A of X | B of Y | C of Z]
type TzXy = μZ.νX.μY.[ Z | A of X | B of Y | C of Z]


(* [fun x:PbcA ↦ x:PaBc] LOOP *)

check TxYz ⊆ TYxz
!check TYxz ⊆ TxYz
!check TxyZ ⊆ TzXy

type S1 = μX.νY.[ A of X | B of Y]
type S2 = νY.μX.[ A of X | B of Y]

check S1 ⊆ S2

!check μX.[A of X] ⊆ μX.[]
!check μX.[] ⊆ ∀X.X

type F(X,Y) = [Z | A of X | B of Y]

check μX.νY.F(X,Y)      ⊆ μX.νY.F(X,F(X,Y))
check μX.νY.F(X,F(X,Y)) ⊆ μX.νY.F(X,Y)
