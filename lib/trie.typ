(* Trie data structure with basic operations. *)

include "prelude.typ"
include "nat.typ"
include "list.typ"

type Trie(K,A) = μT.{value : Option(A); map : List(K × T)}

val empty : ∀A K.Trie(K,A) = {value = None; map = []}

val rec singleton : ∀A K.List(K) → A → Trie(K,A) =
  fun ks v →
    case ks of
    | []    → {value = Some(v); map = []}
    | k::ks → {value = None   ; map = ((k, singleton ks v)::[])}

val rec insert : ∀A K.(K → K → Bool) → Trie(K,A) → List(K) → A → Trie(K,A) =
  fun eq t ks v →
    let A, K such that t : Trie(K,A) in
    case ks of
    | []    → {value = Some(v); map = t.map}
    | k::ks →
        (case assoc (eq k) (t.map : List(K × Trie(K,A))) of
         | None   → {value = t.value; map = ((k, singleton ks v)::t.map)}
         | Some u →
             let r  = insert eq u ks v in
             let rs =
               filter (fun e → neg (eq k e.1)) (t.map : List(K × Trie(K,A)))
             in
             {value = t.value; map = ((k, r)::rs)})

val rec find : ∀A K.(K → K → Bool) → Trie(K,A) → List(K) → Option(A) =
  fun eq t ks →
    let A, K such that t : Trie(K,A) in
    case ks of
    | []    → t.value
    | k::ks →
        (case assoc (eq k) (t.map : List(K × Trie(K,A))) of
         | None   → None
         | Some t → find eq t ks)

val rec size : ∀A K.Trie(K,A) → Nat =
  fun t →
    case t.map of
    | []    → (case t.value of None → Z | Some _ → S Z)
    | u::ts → add (size u.2) (size {value = t.value; map = ts})
