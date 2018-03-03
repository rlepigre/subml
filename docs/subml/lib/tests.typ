check ∀X.X ⊆ ∃X.X
!check ∃X.X ⊆ ∀X.X

type I = ∀X.(X → X)
type I' = ∃X.(X → X)

check I ⊆ I'
!check I' ⊆ I

type N = ∀X.((X → X) → (X → X))

check N ⊆ I → I
check N ⊆ I' → I'
check N ⊆ I → I'
!check N ⊆ I' → I

type F(K) = ∀X.(X → (K → X) → X)
type S = μK.F(K)
type G = νK.F(K)

check S ⊆ G
!check G ⊆ S

check S ⊆ F(S)
check S ⊆ F(F(S))
check F(S) ⊆ S
check F(F(S)) ⊆ S

check G ⊆ F(G)
check G ⊆ F(F(G))
check F(G) ⊆ G
check F(F(G)) ⊆ G

check μX.F(F(X)) ⊆ S
check S ⊆ μX.F(F(X))
check μX.F(F(X)) ⊆ μX.F(F(F(X)))
check μX.F(F(F(X))) ⊆ μX.F(F(X))

check νX.F(F(X)) ⊆ G
check G ⊆ νX.F(F(X))
check νX.F(F(X)) ⊆ νX.F(F(F(X)))
check νX.F(F(F(X))) ⊆ νX.F(F(X))

type P1(A,B) = μX.(X → A) → B
type P2(A,B) = (νX.(X → B) → A) → B
type P3(A,B) = (μX.(X → B) → A) → B
type P4(A,B) = νX.(X → A) → B

type A = [A]
type B = [B]

check P1(A,B) ⊆ P2(A,B)
check P2(A,B) ⊆ P1(A,B)
check P1(A,B) ⊆ P3(A,B)
check P1(A,B) ⊆ P4(A,B)
check P2(A,B) ⊆ P3(A,B)
check P2(A,B) ⊆ P4(A,B)
check P4(A,B) ⊆ P3(A,B)
check P3(A,B) ⊆ P4(A,B)
!check P4(A,B) ⊆ P2(A,B)
!check P4(A,B) ⊆ P1(A,B)
!check P3(A,B) ⊆ P2(A,B)
!check P3(A,B) ⊆ P1(A,B)

type F(X,Y) = [ A of X | B of Y | Nil ]
type T1 = μX.F(X,X)
type T2 = μX.F(X,F(X,X))
type T3 = μX.F(F(X,X),X)
type T4 = μX.F(F(X,X),F(X,X))

check T1 ⊆ T2
check T1 ⊆ T3
check T1 ⊆ T4
check T2 ⊆ T1
check T2 ⊆ T3
check T2 ⊆ T4
check T3 ⊆ T1
check T3 ⊆ T2
check T3 ⊆ T4
check T4 ⊆ T1
check T4 ⊆ T2
check T4 ⊆ T3

type T5 = μX.F(μY.F(X,Y), X)

check T1 ⊆ T5
check T2 ⊆ T5
check T3 ⊆ T5
check T4 ⊆ T5
check T5 ⊆ T1
check T5 ⊆ T2
check T5 ⊆ T3
check T5 ⊆ T4

type T6 = μX.F(μY.F(X,Y), μY.F(Y,X))

check T1 ⊆ T6
check T2 ⊆ T6
check T3 ⊆ T6
check T4 ⊆ T6
check T5 ⊆ T6
check T6 ⊆ T1
check T6 ⊆ T2
check T6 ⊆ T3
check T6 ⊆ T4
check T6 ⊆ T5

type T7 = μX.F(νY.F(X,Y), μY.F(Y,X))
type T8 = μX.F(μY.F(X,Y), νY.F(Y,X))
type T9 = μX.F(νY.F(X,Y), νY.F(Y,X))

check T6 ⊆ T7
check T6 ⊆ T8
check T6 ⊆ T9
check T7 ⊆ T9
check T8 ⊆ T9
!check T7 ⊆ T8
!check T8 ⊆ T7
!check T9 ⊆ T7
!check T9 ⊆ T8
!check T8 ⊆ T7
!check T7 ⊆ T6
!check T8 ⊆ T6
!check T9 ⊆ T6

type T10 = μX.F(X,μY.F(Y,μZ.F(X,Z)))

check T1 ⊆ T10
check T2 ⊆ T10
check T3 ⊆ T10
check T4 ⊆ T10
check T5 ⊆ T10
check T6 ⊆ T10
check T10 ⊆ T1
check T10 ⊆ T2
check T10 ⊆ T3
check T10 ⊆ T4
check T10 ⊆ T5
check T10 ⊆ T6

type T11 = μX.F(X,νY.F(Y,μZ.F(X,Z)))

check T10 ⊆ T11
!check T11 ⊆ T10
