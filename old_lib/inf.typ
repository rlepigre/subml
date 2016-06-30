(* inf normal sur les entiers de Church (ni celui de Morley, ni celui de David *)
include "church.typ";
include "prod.typ";

let easy_inf n:Nat m:Nat =
  let A u m =
    let H = λc. pair (S (pi1 c)) (S (u (pi1 c))) in
    m H (pair 0 0) False in
  n A (λp.0) m
;

(*include "inf.typ";*)