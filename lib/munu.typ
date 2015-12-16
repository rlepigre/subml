
type T1 = μX νY [ Z | A of X | B of Y]
type T2 = νY νX [ Z | A of X | B of Y]

check T1 ⊂ T2

type S1 = μX νY [ A of X | B of Y]
type S2 = νY νX [ A of X | B of Y]

check S1 ⊂ S2

set texfile "test.tex"
latex { we have $#!S1# \subset #!S2#$ }
