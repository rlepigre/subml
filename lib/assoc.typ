(* Association lists implemented with lists. *)

include "prelude.typ"
include "list.typ"

type Assoc(K,V) = {eq : K → K → Bool; list : List(K × V)}

val create : ∀K.(K → K → Bool) → ∀V.Assoc(K,V) =
  fun eq → {eq = eq; list = []}

val insert : ∀K V.K → V → Assoc(K,V) → Assoc(K,V) =
  fun k v asc → {eq = asc.eq; list = ((k,v)::asc.list)}

val delete : ∀K V.K → Assoc(K,V) → Assoc(K,V) =
  fun k asc →
    let list = filter (fun c → neg (asc.eq k c.1)) asc.list in
    {eq = asc.eq; list = list}

val update : ∀K V.K → (Option(V) → V) → Assoc(K,V) → Assoc(K,V) =
  fun k f asc →
    let K,V such that asc : Assoc(K,V) in
    let rec aux : List(K × V) → List(K × V) = fun l →
      case l of
      | []   → (k, f None)::[]
      | c::l → (if asc.eq k c.1 then (k, f (Some c.2)) else c) :: aux l
    in
    {eq = asc.eq; list = aux asc.list}

val rec find : ∀K V.Assoc(K,V) → K → Option(V) =
  fun asc k →
    case asc.list of
    | []   → None
    | c::l → if asc.eq k c.1 then Some c.2
             else find {eq = asc.eq; list = l} k

val assoc_map : ∀K A B.(A → B) → Assoc(K,A) → Assoc(K,B) =
  fun f asc → {eq = asc.eq; list = map (fun c → (c.1, f c.2)) asc.list}

val assoc_iter : ∀K V.(K → V → {}) → Assoc(K,V) → {} =
  fun f asc → iter (fun c → f c.1 c.2) asc.list

(* NOTE: [Assoc(K,V)] would be a subtype of [List(K × V)] if we had default
   fields for records. *)
val assoc_to_list : ∀K V.Assoc(K,V) → List(K × V) =
  fun asc → asc.list

val list_to_assoc : ∀K V.(K → K → Bool) → List(K × V) → Assoc(K,V) =
  fun eq l → {eq = eq; list = l}
