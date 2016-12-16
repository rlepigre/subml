(* Expand all dor projection in dotproj.typ *)

val pair : ∀A ∀B (A → B → A * B) = fun x y → (x, y)

val fst : ∀A ∀B (A * B → A) = fun x → x.1

type FM(X) = { e : X; op : X → X → X }
type Monoid = ∃X FM(X)

val prod : Monoid → Monoid → Monoid = fun m1 m2 →
  { e  : εX(m1∈FM(X)) * εX(m2∈FM(X)) = (m1.e, m2.e);
    op : εX(m1∈FM(X)) * εX(m2∈FM(X)) →  εX(m1∈FM(X)) * εX(m2∈FM(X)) →  εX(m1∈FM(X)) * εX(m2∈FM(X))
       = (fun z1 z2 → (m1.op z1.1 z2.1, m2.op z1.2 z2.2));
  }

type Ring(X) = { e:X; add:X → X → X; opp:X → X; mul:X → X → X}
type FVS(X,V) = { r:Ring(X); mul:X → V → V; add:V → V → V}
type VSpace(X) = ∃V FVS(X,V)

val vprod : ∀X VSpace(X) → VSpace(X) → VSpace(X) = fun vs1 vs2 →
  let X such that _ : VSpace(X) in
  {
  r = vs1.r;
  mul = (fun x v → (vs1.mul x v.1, vs2.mul x v.2)
      : (εV(vs1∈FVS(X,V))  * εV(vs2∈FVS(X,V))));
  add = (fun v1 v2 → (vs1.add v1.1 v2.1, vs2.add v1.2 v2.2)
      : (εV(vs1∈FVS(X,V))  * εV(vs2∈FVS(X,V))));
  }

type FC(O,M) = { dom : M → O; cod : M → O; cmp : M → M → M }
type Cat = ∃M ∃O FC(O,M)

val dual : Cat → Cat = fun c →
  { dom : εM(c∈∃O FC(O,M)) → εO(c∈FC(O,εM(c∈∃O FC(O,M)))) = c.cod;
    cod : εM(c∈∃O FC(O,M)) → εO(c∈FC(O,εM(c∈∃O FC(O,M)))) = c.dom;
    cmp : εM(c∈∃O FC(O,M)) → εM(c∈∃O FC(O,M)) → εM(c∈∃O FC(O,M)) = (fun x y → c.cmp y x);
  }
