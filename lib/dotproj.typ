
val pair : ∀A ∀B (A → B → A * B) = fun x y → (x, y)

val fst : ∀A ∀B (A * B → A) = fun x → x.1

type monoid = ∃X { e : X; op : X -> X -> X }

val prod : monoid -> monoid -> monoid = fun m1 m2 →
  { e  : m1.X * m2.X = (m1.e, m2.e);
    op : m1.X * m2.X → m1.X * m2.X → m1.X * m2.X
       = fun (z1:m1.X * m2.X) (z2:m1.X * m2.X) → (m1.op z1.1 z2.1, m2.op z1.2 z2.2);
  }

type ring(X) = { e:X; add:X → X → X; opp:X → X; mul:X → X → X}
type vspace(X) = ∃V { r:ring(X); mul:X → V → V; add:V → V → V}

val vprod : ∀X vspace(X) → vspace(X) → vspace(X) = fun vs1 vs2 → {
  r = vs1.r;
  mul = fun x v → (vs1.mul x v.1, vs2.mul x v.2) : (vs1.V * vs2.V);
  add = fun v1 v2 → (vs1.add v1.1 v2.1, vs2.add v1.2 v2.2) : (vs1.V * vs2.V);
}

type cat = ∃O ∃M { dom : M → O; codom : M → O; compose : M → M → M }

val dual : cat → cat = fun c →
  { dom : c.M → c.O = c.codom;
    codom : c.M → c.O = c.dom;
    compose : c.M → c.M → c.M = fun x y → c.compose y x;
  }