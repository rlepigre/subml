(* A type for binary trees. *)
type SNode(A,T) = {value : A; left : T; right : T}
type Tree(A) = μX [Leaf | Node of SNode(A,X)]

(* A type for red-black trees. *)
type RBNode(A,T) = {value : A; color : [R | B]; left : T; right : T}
type RBTree(A) = μX [Leaf | Node of RBNode(A,X)]

(* A red-black tree can also be used as a simple binary tree. *)
check RBTree({}) ⊆ Tree({})

(* Lookup function on simple binary trees. *)
val rec contains : ∀X (X → X → Cmp) → X → Tree(X) → Bool = fun cmp e t ↦
  case t of
  | Leaf   → fls
  | Node n →
     (case cmp e n.value of
      | Eq → tru
      | Ls → contains cmp e n.left
      | Gt → contains cmp e n.right)

(* The same function can be used on red-black trees. *)
val containsRB : ∀X (X → X → Cmp) → X → RBTree(X) → Bool =
  contains



(* Shortcut function to build a red-black tree node. *)
val node : ∀X X → [R | B] → RBTree(X) → RBTree(X) → RBNode(X, RBTree(X)) =
  fun e c l r ↦ {value = e; color = c; left = l; right = r}

(* Color in black the root of a tree. If the strict subtrees of the input
   tree respect the invariants, then so does the output tree. *)
val blackRoot : ∀X RBTree(X) → RBTree(X) = fun t ↦
  case t of
  | Leaf   → Leaf
  | Node n → Node (node n.value (B) n.left n.right)

(* Local balancing function. *)
val balance : ∀X RBNode(X, RBTree(X)) → RBTree(X) = fun n ↦
  case n.color of R → Node n | B →
    (case n.left of
     | Node nl →
       (case nl.color of
        | R →
          (case nl.left of
           | Node nll →
             (case nll.color of
              | R →
                (let l = node nll.value (B) nll.left nll.right in
                 let r = node n.value (B) nl.right n.right in
                 Node (node nl.value (R) (Node l) (Node r)))
              | B →
                (case nl.right of
                 | Node nlr →
                   (case nlr.color of
                    | R →
                      (let l = node nl.value (B) nl.left nlr.left in
                       let r = node n.value (B) nlr.right n.right in
                        Node (node nlr.value (R) (Node l) (Node r)))
                    | B →
                      (case n.right of
                       | Node nr →
                         (case nr.color of
                          | R →
                            (case nr.left of
                             | Node nrl →
                               (case nrl.color of
                                | R →
                                  (let l = node n.value (B) n.left nrl.left in
                                   let r = node nrl.value (B) nrl.right nr.right in
                                   Node (node nr.value (R) (Node l) (Node r)))
                                | B →
                                  (case nr.right of
                                   | Node nrr →
                                     (case nrr.color of
                                      | R →
                                        (let l = node n.value (B) n.left nr.left in
                                         let r = node nrr.value (B) nrr.left nrr.right in
                                         Node (node nr.value (R) (Node l) (Node r)))
                                      | B → Node n)
                                   | Leaf     → Node n))
                             | Leaf     →
                               (case nr.right of
                               | Node nrr →
                                 (case nrr.color of
                                  | R →
                                    (let l = node n.value (B) n.left nr.left in
                                     let r = node nrr.value (B) nrr.left nrr.right in
                                     Node (node nr.value (R) (Node l) (Node r)))
                                  | B → Node n)
                               | Leaf     → Node n))
                          | B → Node n)
                       | Leaf    → Node n))
                 | Leaf     →
                   (case n.right of
                    | Node nr →
                      (case nr.color of
                       | R →
                         (case nr.left of
                          | Node nrl →
                            (case nrl.color of
                             | R →
                               (let l = node n.value (B) n.left nrl.left in
                                let r = node nrl.value (B) nrl.right nr.right in
                                Node (node nr.value (R) (Node l) (Node r)))
                             | B →
                               (case nr.right of
                                | Node nrr →
                                  (case nrr.color of
                                   | R →
                                     (let l = node n.value (B) n.left nr.left in
                                      let r = node nrr.value (B) nrr.left nrr.right in
                                      Node (node nr.value (R) (Node l) (Node r)))
                                   | B → Node n)
                                | Leaf     → Node n))
                          | Leaf     →
                            (case nr.right of
                            | Node nrr →
                              (case nrr.color of
                               | R →
                                 (let l = node n.value (B) n.left nr.left in
                                  let r = node nrr.value (B) nrr.left nrr.right in
                                  Node (node nr.value (R) (Node l) (Node r)))
                               | B → Node n)
                            | Leaf     → Node n))
                       | B → Node n)
                    | Leaf    → Node n)))
           | Leaf     → Node n)
        | B →
          (case n.right of
           | Node nr →
             (case nr.color of
              | R →
                (case nr.left of
                 | Node nrl →
                   (case nrl.color of
                    | R →
                      (let l = node n.value (B) n.left nrl.left in
                       let r = node nrl.value (B) nrl.right nr.right in
                       Node (node nr.value (R) (Node l) (Node r)))
                    | B →
                      (case nr.right of
                       | Node nrr →
                         (case nrr.color of
                          | R →
                            (let l = node n.value (B) n.left nr.left in
                             let r = node nrr.value (B) nrr.left nrr.right in
                             Node (node nr.value (R) (Node l) (Node r)))
                          | B → Node n)
                       | Leaf     → Node n))
                 | Leaf     →
                   (case nr.right of
                   | Node nrr →
                     (case nrr.color of
                      | R →
                        (let l = node n.value (B) n.left nr.left in
                         let r = node nrr.value (B) nrr.left nrr.right in
                         Node (node nr.value (R) (Node l) (Node r)))
                      | B → Node n)
                   | Leaf     → Node n))
              | B → Node n)
           | Leaf    → Node n))
     | Leaf    →
       (case n.right of
        | Node nr →
          (case nr.color of
           | R →
             (case nr.left of
              | Node nrl →
                (case nrl.color of
                 | R →
                   (let l = node n.value (B) n.left nrl.left in
                    let r = node nrl.value (B) nrl.right nr.right in
                    Node (node nr.value (R) (Node l) (Node r)))
                 | B →
                   (case nr.right of
                    | Node nrr →
                      (case nrr.color of
                       | R →
                         (let l = node n.value (B) n.left nr.left in
                          let r = node nrr.value (B) nrr.left nrr.right in
                          Node (node nr.value (R) (Node l) (Node r)))
                       | B → Node n)
                    | Leaf     → Node n))
              | Leaf     →
                (case nr.right of
                | Node nrr →
                  (case nrr.color of
                   | R →
                     (let l = node n.value (B) n.left nr.left in
                      let r = node nrr.value (B) nrr.left nrr.right in
                      Node (node nr.value (R) (Node l) (Node r)))
                   | B → Node n)
                | Leaf     → Node n))
           | B → Node n)
        | Leaf    → Node n))
                

val rec insert_aux : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t ↦
  case t of
  | Leaf   → Node (node e (R) (Leaf) (Leaf))
  | Node n →
    (case cmp e n.value of
     | Eq → t
     | Ls → let l = insert_aux cmp e n.left in
            balance (node n.value n.color l n.right)
     | Gt → let r = insert_aux cmp e n.right in
            balance (node n.value n.color n.left r))

val insert : ∀X (X → X → Cmp) → X → RBTree(X) → RBTree(X) = fun cmp e t ↦
  blackRoot (insert_aux cmp e t)


include "lib/nat.typ"
type NTree = RBTree(Nat)

val insert : Nat → NTree → NTree = insert compare

val test : NTree = insert (S Z) (insert (Z) (insert (S S Z) (Leaf)))
