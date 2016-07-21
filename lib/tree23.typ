

type Tree23(A,B) = μT [
  Nil
| Node2 of T × A × B × T
| Node3 of T × A × B × T × A × B × T ]

val rec search : ∀A∀B (A → A → Cmp) → A → Tree23(A,B) → Option(B) = fun compare x t →
  case t of
  | Nil → None
  | Node2(t1,y,d,t2) →
    (case compare x y of
    | Eq → Some d
    | Ls → search compare x t1
    | Gt → search compare x t2)
  | Node3(t1,y1,d1,t2,y2,d2,t3) →
    (case compare x y1 of
    | Eq → Some d1
    | Ls → search compare x t1
    | Gt →
    (case compare x y2 of
    | Eq → Some d2
    | Ls → search compare x t2
    | Gt → search compare x t3))

type ITree23(A,B) = [
  Nil
| Node2 of Tree23(A,B) × A × B × Tree23(A,B)
| INode2 of Tree23(A,B) × A × B × Tree23(A,B) (* increase in size *)
| Node3 of Tree23(A,B) × A × B × Tree23(A,B) × A × B × Tree23(A,B) ]

check Tree23([A],[B]) ⊂ ITree23([A],[B])

val node4 = fun t →
  let (t1,y1,d1,t2,y2,d2,t3,y3,d3,t4) = t in
    INode2(Node2(t1,y1,d1,t2),y2,d2,Node2(t3,y3,d3,t4))

val rec insert_aux : ∀A∀B (A → A → Cmp) → A → B → Tree23(A,B) → ITree23(A,B) =
  fun compare x d t →
  case t of
  | Nil → INode2(Nil, x, d, Nil)
  | Node2(t1,y0,d0,t2) →
    (case compare x y0 of
    | Eq → Node2(t1,y0,d,t2)
    | Ls → (case insert_aux compare x d t1 of
           | INode2(t11,y1,d1,t12) → Node3(t11,y1,d1,t12,y0,d0,t2)
           | t1 → Node2(t1,y0,d0,t2))
    | Gt → (case insert_aux compare x d t2 of
           | INode2(t21,y1,d1,t22) → Node3(t1,y0,d0,t21,y1,d1,t22)
           | t2 → Node2(t1,y0,d0,t2)))
  | Node3(t1,y1,d1,t2,y2,d2,t3) →
    (case compare x y1 of
    | Eq → Node3(t1,y1,d,t2,y2,d2,t3)
    | Ls → (case insert_aux compare x d t1 of
           | INode2(t11,y11,d11,t12) → node4(t11,y11,d11,t12,y1,d1,t2,y2,d2,t3)
           | t1 → Node3(t1,y1,d1,t2,y2,d2,t3))
    | Gt →
    (case compare x y2 of
    | Eq → Node3(t1,y1,d1,t2,y2,d,t3)
    | Ls → (case insert_aux compare x d t2 of
           | INode2(t21,y21,d21,t22) → node4(t1,y1,d1,t21,y21,d21,t22,y2,d2,t3)
           | t2 → Node3(t1,y1,d1,t2,y2,d2,t3))
    | Gt → (case insert_aux compare x d t3 of
           | INode2(t31,y31,d31,t32) → node4(t1,y1,d1,t2,y2,d2,t31,y31,d31,t32)
           | t3 → Node3(t1,y1,d1,t2,y2,d2,t3))))

val insert : ∀A∀B (A → A → Cmp) → A → B → Tree23(A,B) → Tree23(A,B) =
  fun compare x d t →
    case insert_aux compare x d t of
    | INode2(t21,y21,d21,t22) →  Node2(t21,y21,d21,t22)
    | t → t

include "lib/nat.typ"

val t0 = insert compare 0 0 Nil
val t1 = insert compare 1 1 t0
val t2 = insert compare 2 2 t1
val t3 = insert compare 3 3 t2
val t4 = insert compare 4 4 t3
val t5 = insert compare 5 5 t4
val t6 = insert compare 6 6 t5
val t7 = insert compare 7 7 t6
val t8 = insert compare 8 8 t7
val t9 = insert compare 9 9 t8
val t10= insert compare 10 10 t9

val rec height : ∀A∀B (Tree23(A,B) → Nat) = fun t →
  case t of
  | Nil → 0
  | Node2(t,_,_,_) → S (height t)
  | Node3(t,_,_,_,_,_,_) → S(height t)

val balanced = fun t →
  let h = height t in
  let rec bal_aux = fun n t →
    case t of
    | Nil → eq n 0
    | Node2(t1,_,_,t2) →
      (case n of Z → Fls | S p → and (bal_aux p t1) (bal_aux p t2))
    | Node3(t1,_,_,t2,_,_,t3) →
      (case n of Z → Fls | S p → and (bal_aux p t1) (and (bal_aux p t2) (bal_aux p t3)))
  in bal_aux h t

eval t10
eval (balanced t10)
