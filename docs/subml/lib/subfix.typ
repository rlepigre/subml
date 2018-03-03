(** Various subtyping tests using fixpoints *)

(* Test of munu alternancy *)
type T1 = μX.νY.[ Z | A of X | B of Y]
type T2 = νY.μX.[ Z | A of X | B of Y]

 check T1 ⊆ T2
!check T2 ⊆ T1

type S1 = μX.νY.[ A of X | B of Y]
type S2 = νY.μX.[ A of X | B of Y]

 check S1 ⊆ S2
!check S2 ⊆ S1

(* test of alternacy with three fixpoint *)
type TxYz = μX.νY.μZ.[ Z | A of X | B of Y | C of Z]
type TxyZ = μX.μY.νZ.[ Z | A of X | B of Y | C of Z]
type TYxz = νY.μX.μZ.[ Z | A of X | B of Y | C of Z]
type TzXy = μZ.νX.μY.[ Z | A of X | B of Y | C of Z]


 check TxYz ⊆ TYxz
!check TYxz ⊆ TxYz
!check TxyZ ⊆ TzXy

(* very simple test *)
!check μX.[A of X] ⊆ μX.[]
!check μX.[] ⊆ ∀X.X

(* unfolding tests *)
type F(X,Y) = [Z | A of X | B of Y]
type G(X)   = F(X,X)

check μX.G(X)           ⊆ μX.G(X)
check μX.G(X)           ⊆ μX.G(G(X))
check μX.G(G(X))        ⊆ μX.G(X)
check μX.G(X)           ⊆ μX.G(G(G(X)))
check μX.G(G(G(X)))     ⊆ μX.G(X)
check μX.G(G(X))        ⊆ μX.G(G(G(X)))
check μX.G(G(G(X)))     ⊆ μX.G(G(X))

check μX.νY.F(X,Y)      ⊆ μX.νY.F(X,F(X,Y))
check μX.νY.F(X,F(X,Y)) ⊆ μX.νY.F(X,Y)
check μX.νY.F(X,Y)      ⊆ μX.νY.F(F(X,Y),Y)
!check μX.νY.F(F(X,Y),Y) ⊆ μX.νY.F(X,Y)

(* unfolding contravariant *)
type F(X) = [Z | A of X → {} ]
type G(X) = [Y | B of X → {} ]

check μX.F(G(X))      ⊆ F(νX.G(F(X)))
check F(νX.G(F(X)))   ⊆ μX.F(G(X))
check νX.F(G(X))      ⊆ F(μX.G(F(X)))
check F(μX.G(F(X)))   ⊆ νX.F(G(X))
