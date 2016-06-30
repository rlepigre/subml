(* test sur les alternances de mu et nu *)
typed; inductive;

type F(K) = ∀X (X → (K → X) → X);
type G(X,K) = (X → (K → X) → X);
type S = μK F(K);
type G = νK F(K);

fun x:S ↦ x:G;
untyped fun x:G ↦ x:S;

fun x:S ↦ x:F(S);
fun x:S ↦ x:F(F(S));
fun x:F(S) ↦ x:S;
fun x:F(F(S)) ↦ x:S;

fun x:G ↦ x:F(G);
fun x:G ↦ x:F(F(G));
fun x:F(G) ↦ x:G;
fun x:F(F(G)) ↦ x:G;

fun x:μX F(F(X)) ↦ x : μX F(X);
fun x:μX F(X) ↦ x : μX F(F(X));
fun x:μX F(F(X)) ↦ x : μX F(F(F(X)));
fun x:μX F(F(F(X))) ↦ x : μX F(F(X));

fun x:νX F(F(X)) ↦ x : νX F(X);
fun x:νX F(X) ↦ x : νX F(F(X));
fun x:νX F(F(X)) ↦ x : νX F(F(F(X)));
fun x:νX F(F(F(X))) ↦ x : νX F(F(X));

type P1(A,B) = μX ((X → A) → B);
type P2(A,B) = νX ((X → B) → A) → B;
type P3(A,B) = μX ((X → B) → A) → B;
type P4(A,B) = νX ((X → A) → B);

∀A ∀B (fun x:P1(A,B) ↦ x:P2(A,B));
∀A ∀B (fun x:P2(A,B) ↦ x:P1(A,B));
∀A ∀B (fun x:P2(A,B) ↦ x:P3(A,B));
∀A ∀B (fun x:P3(A,B) ↦ x:P4(A,B));
∀A ∀B (fun x:P4(A,B) ↦ x:P3(A,B));
untyped ∀A ∀B (fun x:P3(A,B) ↦ x:P2(A,B));
untyped ∀A ∀B (fun x:P4(A,B) ↦ x:P2(A,B));
untyped ∀A ∀B (fun x:P3(A,B) ↦ x:P1(A,B));
untyped ∀A ∀B (fun x:P4(A,B) ↦ x:P1(A,B));

type F2(K,L) = ∀X (X → (K → X) → (L → X) → X);
type P1 = μK F2(K,K);
type P2 = μK1 μK2 F2(K1,K2);
type P3 = μK1 νK2 F2(K1,K2); (* if K1 is for zeros : only a finite number of 0 *)
type P4 = νK2 μK1 F2(K1,K2); (* only finitely many consecutive zeros *)
type P5 = νK2 νK1 F2(K1,K2);
type P6 = νK F2(K,K);

fun x:P2 ↦ x:P1;
fun x:P1 ↦ x:P2;
fun x:P2 ↦ x:P3;
fun x:P3 ↦ x:P4;
untyped fun x:P3 ↦ x:P2;
untyped fun x:P4 ↦ x:P3;
fun x:P4 ↦ x:P5;
untyped fun x:P5 ↦ x:P4;
fun x:P5 ↦ x:P6;
fun x:P6 ↦ x:P5;

type Pabc = μXμYμZ [ A of X | B of Y | C of Z ];
type Pabc' = μXμY [ A of X | B of X | C of Y ];
type Pabc'' = μXμY [ A of X | B of Y | C of Y ];
type Pabc''' = μXμY [ A of X | B of Y | C of X ];
type Pabc'''' = μX [ A of X | B of X | C of X ];

type Qabc = μXμYμZ { A : X ; B : Y ; C : Z };
type Qabc' = μXμY { A : X ; B : X ; C : Y };
type Qabc'' = μXμY { A : X ; B : Y ; C : Y };
type Qabc''' = μXμY { A : X ; B : Y ; C : X };
type Qabc'''' = μX { A : X ; B : X ; C : X };

fun x:Pabc ↦ x:Pabc';
fun x:Pabc ↦ x:Pabc'';
fun x:Pabc ↦ x:Pabc''';
fun x:Pabc ↦ x:Pabc'''';
fun x:Pabc' ↦ x:Pabc'';
fun x:Pabc' ↦ x:Pabc''';
fun x:Pabc' ↦ x:Pabc''';
fun x:Pabc'' ↦ x:Pabc''';
fun x:Pabc'' ↦ x:Pabc'''';
fun x:Pabc''' ↦ x:Pabc'''';

fun x:Pabc' ↦ x:Pabc;
fun x:Pabc'' ↦ x:Pabc;
fun x:Pabc''' ↦ x:Pabc;
fun x:Pabc'''' ↦ x:Pabc;
fun x:Pabc'' ↦ x:Pabc';
fun x:Pabc''' ↦ x:Pabc';
fun x:Pabc'''' ↦ x:Pabc';
fun x:Pabc''' ↦ x:Pabc'';
fun x:Pabc'''' ↦ x:Pabc'';
fun x:Pabc'''' ↦ x:Pabc''';

type PAbc = νXμYμZ [ A of X | B of Y | C of Z ];
type PbAc = μYνXμZ [ A of X | B of Y | C of Z ];
type PbcA = μYμZνX [ A of X | B of Y | C of Z ];
type PBac = νYμXμZ [ A of X | B of Y | C of Z ];
type PaBc = μXνYμZ [ A of X | B of Y | C of Z ];
type PacB = μXμZνY [ A of X | B of Y | C of Z ];
type PABc = νXνYμZ [ A of X | B of Y | C of Z ];
type PAcB = νXμZνY [ A of X | B of Y | C of Z ];
type PcAB = μZνXνY [ A of X | B of Y | C of Z ];
type PABc' = νXμZ [ A of X | B of X | C of Z ];
type PcAB' = μZνX [ A of X | B of X | C of Z ];

type QAbc = νXμYμZ { A : X ; B : Y ; C : Z };
type QbAc = μYνXμZ { A : X ; B : Y ; C : Z };
type QbcA = μYμZνX { A : X ; B : Y ; C : Z };
type QBac = νYμXμZ { A : X ; B : Y ; C : Z };
type QaBc = μXνYμZ { A : X ; B : Y ; C : Z };
type QacB = μXμZνY { A : X ; B : Y ; C : Z };
type QABc = νXνYμZ { A : X ; B : Y ; C : Z };
type QAcB = νXμZνY { A : X ; B : Y ; C : Z };
type QcAB = μZνXνY { A : X ; B : Y ; C : Z };
type QABc' = νXμZ { A : X ; B : X ; C : Z };
type QcAB' = μZνX { A : X ; B : X ; C : Z };

# test avec un nu, position du nu
fun x:PbcA ↦ x:PbAc;
fun x:PbAc ↦ x:PAbc;
fun x:PbcA ↦ x:PAbc;
untyped fun x:PAbc ↦ x:PbAc;
untyped fun x:PAbc ↦ x:PbcA;
untyped fun x:PbAc ↦ x:PbcA;

# un nu et sans nu
fun x:Pabc ↦ x:PAbc;
fun x:Pabc ↦ x:PbAc;
fun x:Pabc ↦ x:PbcA;
fun x:Pabc' ↦ x:PAbc;
fun x:Pabc' ↦ x:PbAc;
fun x:Pabc' ↦ x:PbcA;
fun x:Pabc'' ↦ x:PAbc;
fun x:Pabc'' ↦ x:PbAc;
fun x:Pabc'' ↦ x:PbcA;
fun x:Pabc''' ↦ x:PAbc;
fun x:Pabc''' ↦ x:PbAc;
fun x:Pabc''' ↦ x:PbcA;
fun x:Pabc'''' ↦ x:PAbc;
fun x:Pabc'''' ↦ x:PbAc;
fun x:Pabc'''' ↦ x:PbcA;

untyped fun x:PAbc ↦ x:Pabc;
untyped fun x:PbAc ↦ x:Pabc;
untyped fun x:PbcA ↦ x:Pabc;
untyped fun x:PAbc ↦ x:Pabc';
untyped fun x:PbAc ↦ x:Pabc';
untyped fun x:PbcA ↦ x:Pabc';
untyped fun x:PAbc ↦ x:Pabc'';
untyped fun x:PbAc ↦ x:Pabc'';
untyped fun x:PbcA ↦ x:Pabc'';
untyped fun x:PAbc ↦ x:Pabc''';
untyped fun x:PbAc ↦ x:Pabc''';
untyped fun x:PbcA ↦ x:Pabc''';
untyped fun x:PAbc ↦ x:Pabc'''';
untyped fun x:PbAc ↦ x:Pabc'''';
untyped fun x:PbcA ↦ x:Pabc'''';

#test avec nu différent de chaque côté
untyped fun x:PAbc ↦ x:PaBc;
untyped fun x:PAbc ↦ x:PBac;
untyped fun x:PAbc ↦ x:PacB;
untyped fun x:PbAc ↦ x:PaBc;
untyped fun x:PbAc ↦ x:PBac;
untyped fun x:PbAc ↦ x:PacB;
(*untyped fun x:PbcA ↦ x:PaBc; LOOP *)
untyped fun x:PbcA ↦ x:PBac;
untyped fun x:PbcA ↦ x:PacB;

#test avec deux nu
fun x:PABc ↦ x:PABc';
fun x:PABc' ↦ x:PABc;
fun x:PcAB ↦ x:PcAB';
fun x:PcAB' ↦ x:PcAB;
fun x:PcAB ↦ x:PAcB;
fun x:PcAB' ↦ x:PAcB;
fun x:PcAB ↦ x:PABc;
fun x:PcAB' ↦ x:PABc;
fun x:PcAB ↦ x:PABc';
fun x:PcAB' ↦ x:PABc';
fun x:PAcB ↦ x:PABc;
fun x:PAcB ↦ x:PABc';

untyped fun x:PABc ↦ x:PAcB;
untyped fun x:PABc' ↦ x:PAcB;
untyped fun x:PABc ↦ x:PcAB;
untyped fun x:PABc' ↦ x:PcAB;
untyped fun x:PABc ↦ x:PcAB';
untyped fun x:PABc' ↦ x:PcAB';
untyped fun x:PAcB ↦ x:PcAB;
untyped fun x:PAcB ↦ x:PcAB';

#un nu avec deux nu
fun x:PbcA ↦ x:PcAB;
fun x:PbcA ↦ x:PcAB';
fun x:PbcA ↦ x:PAcB;
fun x:PbAc ↦ x:PAcB;
fun x:PAbc ↦ x:PAcB;
fun x:PAbc ↦ x:PABc;
fun x:PAbc ↦ x:PABc';
untyped fun x:PbAc ↦ x:PcAB;
untyped fun x:PAbc ↦ x:PcAB;

type PABC = νXνYνZ [ A of X | B of Y | C of Z ];

type F(X,Y) = [ A of X | B of Y | Nil ];
type T1 = μX F(X,X);
type T2 = μX F(X,F(X,X));
type T3 = μX F(F(X,X),X);
type T4 = μX F(F(X,X),F(X,X));

fun x:T1 ↦ x:T2;
fun x:T1 ↦ x:T3;
fun x:T1 ↦ x:T4;
fun x:T2 ↦ x:T3;
fun x:T2 ↦ x:T4;
fun x:T3 ↦ x:T4;
fun x:T2 ↦ x:T1;
fun x:T3 ↦ x:T1;
fun x:T4 ↦ x:T1;
fun x:T3 ↦ x:T2;
fun x:T4 ↦ x:T2;
fun x:T4 ↦ x:T3;

type T5 = μX F(μY F(X,Y), X);
fun x:T1 ↦ x:T5;
fun x:T2 ↦ x:T5;
fun x:T3 ↦ x:T5;
fun x:T4 ↦ x:T5;
fun x:T5 ↦ x:T1;
fun x:T5 ↦ x:T2;
fun x:T5 ↦ x:T3;
fun x:T5 ↦ x:T4;

type T6 = μX F(μY F(X,Y), μY F(Y,X));
fun x:T1 ↦ x:T6;
fun x:T2 ↦ x:T6;
fun x:T3 ↦ x:T6;
fun x:T4 ↦ x:T6;
fun x:T5 ↦ x:T6;
fun x:T6 ↦ x:T1;
fun x:T6 ↦ x:T2;
fun x:T6 ↦ x:T3;
fun x:T6 ↦ x:T4;
fun x:T6 ↦ x:T5;

type T7 = μX F(νY F(X,Y), μY F(Y,X));
type T8 = μX F(μY F(X,Y), νY F(Y,X));
type T9 = μX F(νY F(X,Y), νY F(Y,X));

fun x:T6 ↦ x:T7;
fun x:T6 ↦ x:T8;
fun x:T6 ↦ x:T9;
fun x:T7 ↦ x:T9;
fun x:T8 ↦ x:T9;
untyped fun x:T7 ↦ x:T8;
untyped fun x:T8 ↦ x:T7;
untyped fun x:T9 ↦ x:T7;
untyped fun x:T9 ↦ x:T8;
untyped fun x:T7 ↦ x:T6;
untyped fun x:T8 ↦ x:T6;
untyped fun x:T9 ↦ x:T6;

type T10 = μX F(X,μY F(Y,μZ F(X,Z)));
fun x:T1 ↦ x:T10;
fun x:T2 ↦ x:T10;
fun x:T3 ↦ x:T10;
fun x:T4 ↦ x:T10;
fun x:T5 ↦ x:T10;
fun x:T6 ↦ x:T10;
fun x:T10 ↦ x:T1;
fun x:T10 ↦ x:T2;
fun x:T10 ↦ x:T3;
fun x:T10 ↦ x:T4;
fun x:T10 ↦ x:T5;
fun x:T10 ↦ x:T6;

type T11 = μX F(X,νY F(Y,μZ F(X,Z)));
fun x:T10 ↦ x:T11;
untyped fun x:T11 ↦ x:T10;
