val pair : ∀A.∀B.(A → B → A × B) = fun x y → (x, y)

val fst : ∀A.∀B.(A × B → A) = fun x → x.1

type Monoid = ∃X.{e : X; op : X → X → X}

val prod : Monoid → Monoid → Monoid = fun m1 m2 →
  { e  : m1.X × m2.X = (m1.e, m2.e);
    op : m1.X × m2.X →  m1.X × m2.X →  m1.X × m2.X
       = (fun z1 z2 → (m1.op z1.1 z2.1, m2.op z1.2 z2.2));
  }

type Ring(X) = {e:X; add:X → X → X; opp:X → X; mul:X → X → X}
type VSpace(X) = ∃V.{r:Ring(X); mul:X → V → V; add:V → V → V}

val vprod : ∀X.VSpace(X) → VSpace(X) → VSpace(X) = fun vs1 vs2 →
  let X such that _ : VSpace(X) in
  { r   = vs1.r
  ; mul = (fun x v → ((vs1.mul x v.1, vs2.mul x v.2) : vs1.V × vs2.V))
  ; add = (fun v1 v2 → ((vs1.add v1.1 v2.1, vs2.add v1.2 v2.2) : vs1.V × vs2.V)) }

type Cat = ∃O.∃M.{dom : M → O; cod : M → O; cmp : M → M → M}

val dual : Cat → Cat = fun c →
  { dom : c.M → c.O = c.cod;
    cod : c.M → c.O = c.dom;
    cmp : c.M → c.M → c.M = (fun x y → c.cmp y x); }
