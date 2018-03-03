(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

include "nat.typ"
include "natbin.typ"

type Key = Bin

type PTree(A) = μT [ Empty | Leaf of Bin * A | Branch of Bin * Bin * T * T ]

val empty : ∀A PTree(A) = Empty

val is_empty : ∀A PTree(A) → Bool =
  fun t → case t of Empty → tru | _ → fls

val zero_bit : Bin → Bin → Bool =
  fun k m → is_zero (land k m)

val rec mem : ∀A Key → PTree(A) → Bool =
  fun k t →
    case t of
    | Empty           → fls
    | Leaf(j,_)       → eq_bin k j
    | Branch(_,m,l,r) → mem k (if zero_bit k m then l else r)

val rec find : ∀A Key → PTree(A) → Option(A) =
  fun k t →
    case t of
    | Empty           → None
    | Leaf(j,x)       → if eq_bin k j then Some x else None
    | Branch(_,m,l,r) → find k (if zero_bit k m then l else r)

val lowest_bit : Bin → Bin =
  fun x → land x (carryless_incr (complement x))

val branching_bit : Bin → Bin → Bin =
  fun p0 p1 → lowest_bit (lxor p0 p1)

val mask : Bin → Bin → Bin =
  fun p m → land p (carryless_decr m)

val join : ∀A Bin → PTree(A) → Bin → PTree(A) → PTree(A) =
  fun p0 t0 p1 t1 →
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then Branch(mask p0 m, m, t0, t1)
    else Branch(mask p0 m, m, t1, t0)

val match_prefix : Bin → Bin → Bin → Bool =
  fun k p m → eq_bin (mask k m) p

val ptree_add : ∀A Key → A → PTree(A) → PTree(A) =
  fun k x t →
    let A such that x : A in
    let rec ins : PTree(A) → PTree(A) = fun t →
      case t of
      | Empty             → Leaf (k,x)
      | Leaf(j,_)         → if eq_bin j k then Leaf (k,x)
                            else join k (Leaf(k,x)) j t
      | Branch(p,m,t0,t1) → if match_prefix k p m then
                              if zero_bit k m then Branch (p, m, ins t0, t1)
                              else Branch (p, m, t0, ins t1)
                                  else join k (Leaf(k,x)) p t
    in
    ins t

val singleton : ∀A Key → A → PTree(A) =
  fun k v → ptree_add k v empty

val branch : ∀A Bin → Bin → PTree(A) → PTree(A) → PTree(A) =
  fun p m t0 t1 →
    case t0 of
    | Empty   → t1
    | _       → (case t1 of Empty → t0 | _ → Branch(p,m,t0,t1))

val remove : ∀A Key → PTree(A) → PTree(A) =
  fun k t →
    let A such that t : PTree(A) in
    let rec rmv : PTree(A) → PTree(A) = fun t →
      case t of
      | Empty             → Empty
      | Leaf(j,_)         → if eq_bin k j then Empty else t
      | Branch(p,m,t0,t1) → if match_prefix k p m then
                              if zero_bit k m then branch p m (rmv t0) t1
                              else branch p m t0 (rmv t1)
                            else t
    in
    rmv t

val rec 2 cardinal : ∀A PTree(A) → Nat =
  fun t →
    case t of
    | Empty             → Z
    | Leaf _            → S Z
    | Branch(_,_,t0,t1) → add (cardinal t0) (cardinal t1)

val rec iter : ∀A (Key → A → {}) → PTree(A) → {} =
  fun f t →
    case t of
    | Empty             → {}
    | Leaf(k,v)         → f k v
    | Branch(_,_,t0,t1) → iter f t0; iter f t1

val rec map : ∀A ∀B (A → B) → PTree(A) → PTree(B) =
  fun f t →
    case t of
    | Empty             → Empty
    | Leaf(k,v)         → Leaf(k, f v)
    | Branch(p,m,t0,t1) → Branch(p, m, map f t0, map f t1)

val rec mapi : ∀A ∀B (Key → A → B) → PTree(A) → PTree(B) =
  fun f t →
    case t of
    | Empty             → Empty
    | Leaf(k,v)         → Leaf(k, f k v)
    | Branch(p,m,t0,t1) → Branch(p, m, mapi f t0, mapi f t1)

val rec fold : ∀A ∀B (Key → A → B → B) → PTree(A) → B → B =
  fun f s acc →
    case s of
    | Empty             → acc
    | Leaf(k,v)         → f k v acc
    | Branch(_,_,t0,t1) → fold f t0 (fold f t1 acc)

val rec for_all : ∀A (Key → A → Bool) → PTree(A) → Bool =
  fun p t →
    case t of
    | Empty             → tru
    | Leaf(k,v)         → p k v
    | Branch(_,_,t0,t1) → and (for_all p t0) (for_all p t1)

val rec exists : ∀A (Key → A → Bool) → PTree(A) → Bool =
  fun p t →
    case t of
    | Empty             → fls
    | Leaf(k,v)         → p k v
    | Branch(_,_,t0,t1) → or (exists p t0) (exists p t1)

val rec filter : ∀A (Key → A → Bool) → PTree(A) → PTree(A) =
  fun p t →
    case t of
    | Empty             → Empty
    | Leaf(k,v)         → if p k v then t else Empty
    | Branch(q,m,t0,t1) → branch q m (filter p t0) (filter p t1)


val partition : ∀A (Key → A → Bool) → PTree(A) → PTree(A) * PTree(A) =
  fun p t →
    let A such that t : PTree(A) in
    let rec part : PTree(A) * PTree(A) → PTree(A) → PTree(A) * PTree(A) =
      fun acc t →
        case t of
        | Empty             → acc
        | Leaf(k,v)         → if p k v then (ptree_add k v acc.1, acc.2)
                              else (acc.1, ptree_add k v acc.2)
        | Branch(_,_,t0,t1) → part (part acc t0) t1
    in
    part (Empty, Empty) t

val rec choose : ∀A PTree(A) → Option(Key * A) =
  fun t →
    case t of
    | Empty           → None
    | Leaf(k,v)       → Some (k,v)
    | Branch(_,_,t,_) → choose t

(*
let split x m =
  let coll k v (l, b, r) =
    if k < x then ptree_add k v l, b, r
    else if k > x then l, b, ptree_add k v r
    else l, Some v, r
  in
  fold coll m (empty, None, empty)

let rec min_binding = function
  | Empty → raise Not_found
  | Leaf (k, v) → (k, v)
  | Branch (_,_,s,t) →
      let (ks, _) as bs = min_binding s in
      let (kt, _) as bt = min_binding t in
      if ks < kt then bs else bt

let rec max_binding = function
  | Empty → raise Not_found
  | Leaf (k, v) → (k, v)
  | Branch (_,_,s,t) →
      let (ks, _) as bs = max_binding s in
      let (kt, _) as bt = max_binding t in
      if ks > kt then bs else bt

let bindings m =
  fold (fun k v acc → (k, v) :: acc) m []

let compare cmp t1 t2 =
  let rec compare_aux t1 t2 = match t1,t2 with
    | Empty, Empty → 0
    | Empty, _ → -1
    | _, Empty → 1
    | Leaf (k1,x1), Leaf (k2,x2) →
        let c = compare k1 k2 in
        if c <> 0 then c else cmp x1 x2
    | Leaf _, Branch _ → -1
    | Branch _, Leaf _ → 1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) →
        let c = compare p1 p2 in
        if c <> 0 then c else
        let c = compare m1 m2 in
        if c <> 0 then c else
        let c = compare_aux l1 l2 in
        if c <> 0 then c else
        compare_aux r1 r2
  in
  compare_aux t1 t2

let equal eq t1 t2 =
  let rec equal_aux t1 t2 = match t1, t2 with
    | Empty, Empty → true
    | Leaf (k1,x1), Leaf (k2,x2) → k1 = k2 && eq x1 x2
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) →
        p1 = p2 && m1 = m2 && equal_aux l1 l2 && equal_aux r1 r2
    | _ → false
  in
  equal_aux t1 t2

let merge f m1 m2 =
  let ptree_add m k = function None → m | Some v → ptree_add k v m in
  let m = fold
    (fun k1 v1 m → ptree_add m k1 (f k1 (Some v1) (find_opt k1 m2))) m1 empty in
  fold (fun k2 v2 m → if mem k2 m1 then m else ptree_add m k2 (f k2 None (Some v2)))
    m2 m
*)
