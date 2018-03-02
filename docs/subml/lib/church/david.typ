(* René David's “inf” function on Church numerals. *)

include "church/bool.typ"
include "church/nat.typ"
include "church/list.typ"

(* Short names for Church-encoded booleans, natural numbers and lists. *)

type B    = CBool
type N    = CNat
type L(A) = CList(A)

type N_Star(O) = ∀X.(((X → O) → (X → O)) → (X → O) → (X → O))

val nstore : ∀O.N_Star(O) → (N → O) → O =
  fun n → n (fun x y → x (fun z → y (s z))) (fun f → f z)

type B_Star(O) = ∀X.((X → O) → (X → O) → (X → O))

val bstore : ∀O.(B_Star(O) → (B → O) → O) =
  fun b → b (fun f → f ctru) (fun f → f cfls)

type L_Star(A,O) = ∀X.((A → (X → O) → (X → O)) → (X → O) → (X → O))

val lstore : ∀O.L_Star(B,O) → (L(B) → O) → O =
  fun l → l
    (fun a → bstore a (fun b r f → r (fun z → f (cns b z))))
    (fun f → f nil)

val test_list : L(B) → N → N → N =
  fun l n m → l (fun b r → b cfls r) ctru n m

val list : N → L(B) =
  fun k → k (cns cfls) (cns ctru nil)

val pred : L(B) → L(B) =
  let f = fun a y b → b (cns a (y ctru)) (cns (neg a) (y a)) in
  fun l → l f (fun _ → nil) cfls

val next : (L(B) → N) → L(B) → N =
  fun g l → test_list l (s (g l)) (lstore (pred l) g)

val dif : N → N → N =
  fun n k → n next (fun _ → z) (list k)

val test : N → N → B → B → B =
  fun n k a b → dif n k (fun _ → a) b

val init : N → N → N → N → B =
  fun _ _ _ _ → ctru

val iteration : (N → N → N → N → B) → (N → N → N → N → B) =
  fun g n m k p →
    let f = fun _ →
      let g = fun _ →
        test n k (test m k (g n m (s k) k) cfls)
          (test m k ctru ((nstore (dif m p) (nstore (dif n p) g)) z z))
      in n g ctru
    in m f cfls

val inf : N → N → B =
  fun n m → s (s (s (s (s (s ( s (s n))))))) iteration init n m z z

val good_inf : N → N → N =
  fun n m → inf n m n m
