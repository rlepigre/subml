(* Binary coding of natural numbers, using Church encoding and typed *)

include "church/bool.typ"
include "church/data.typ"
include "church/error.typ"

type FBin(K) = ∀X((K → X) → (K → X) → X → X)
type Bin = μK FBin(K)

(* Binary representation with lower bits first *)
val end : Bin = λz o e.e        (* end of the representation *)
val sz  : Bin → Bin = λn z o e.z n (* adds a zero *)
val nsz  : Bin → Bin = λn.n (λnp z o e.z n) (λnp z o e.z n) end
(* adds a zero and keep a normal representation *)
val so  : Bin → Bin = λn z o e.(o n)   (* adds a one *)

(*
We will only use "normal" represention. This means we will assume
that there is never some useless zeros at the end of a number.  To
do this we need two functions which add a zero or a one in front of
a normal representation, keeping it normal and caring about errors.
*)


val esz : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (sz x))
val ensz : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (nsz x))
val eso : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (so x))

(* Test for zero (works on non normal representation)*)
val rec is_zero : Bin → CBool = λn.n
  (λnp.is_zero np)
  (λnp.cfls)
  ctru

(* Successor and zero *)
val zero = end
val rec s : Bin → Bin = λn.n (λnp.so np) (λnp.sz (s np)) (so end)

(* Predecessor *)
val rec pred : Bin → Err(Bin) = λn.n
  (λnp.eso (pred np)) (λnp.unit (nsz np)) error

(* Addition *)
val rec add_aux : Bin → Bin → CBool → Bin
  = λn m r. n
  (λnp.m
    (λmp.cond r (so (add_aux np mp cfls)) (sz (add_aux np mp cfls)))
    (λmp.cond r (sz (add_aux np mp ctru)) (so (add_aux np mp cfls)))
    (cond r (so np) (sz np)))
  (λnp.m
    (λmp.cond r (sz (add_aux np mp ctru)) (so (add_aux np mp cfls)))
    (λmp.cond r (so (add_aux np mp ctru)) (sz (add_aux np mp ctru)))
    (cond r (sz (s np)) (so np)))
  (cond (neg r) m (s m)) (* FIXME: neg r to to the correct forall elim *)

val add = λn m.add_aux n m cfls

(* Multiplication *)
val rec mul : Bin → Bin → Bin = λn m.(n
  (λnp.sz (mul np m))
  (λnp.add m (sz (mul np m)))
  end)

(* Subtraction *)
val rec sub_aux : Bin → Bin → CBool → Err(Bin) = λn m r. n
  (λnp.m
    (λmp.r (eso (sub_aux np mp ctru)) (ensz (sub_aux np mp cfls)))
    (λmp.r (ensz (sub_aux np mp ctru)) (eso (sub_aux np mp ctru)))
    (r (eso (pred np)) (unit (nsz np))))
  (λnp.m
    (λmp.r (ensz (sub_aux np mp cfls)) (eso (sub_aux np mp cfls)))
    (λmp.r (eso (sub_aux np mp ctru)) (ensz (sub_aux np mp cfls)))
    (r (unit (nsz np)) (unit (so np))))
  (r error (neg (is_zero m) error (unit end))) (* FIXME: same as above *)
val sub = λn m.sub_aux n m cfls

(* Some numbers *)
val 0 = end
val 1 = s 0
val 2 = s 1
val 3 = s 2
val 4 = s 3
val 5 = s 4
val 6 = s 5
val 7 = s 6
val 8 = s 7
val 9 = s 8
val 10 = s 9
val 20 = add 10 10
val 30 = add 20 10
val 40 = add 30 10
val 100 = mul 10 10

(* bad Division and modulo *) (* FIXME: explain why bad ! *)
val rec euclide : Bin → Bin → Pair(Bin,Bin) = λn m. n
  (λnp. (euclide np m (λq r.
      catch (sub (nsz r) m)
        (λnr. pair (so q) nr)
        (pair (nsz q) (nsz r)))))
  (λnp. (euclide np m (λq r.
      catch (sub (so r) m)
        (λnr. pair (so q) nr)
        (pair (nsz q) (so r)))))
  (pair end end)


val div : Bin → Bin → Bin = λn m. pi1 (euclide n m)
val mod : Bin → Bin → Bin = λn m. pi2 (euclide n m)

(* Another Division and modulo *)
val rec reverse' : Bin → Bin → Bin = fun n a →
  n (λnp.reverse' np (sz a)) (λnp.reverse' np (so a)) a
val reverse = fun n → reverse' n end

(* termination check fails …

val euclide = fun n m →
  let rec euclide' : Bin → Bin → Bin → Pair(Bin,Bin) = fun n r q →
    catch (sub n m)
      (λ(nn:Bin). r (λ(nr:Bin).euclide' (nsz nn) nr (so q))
              (λ(nr:Bin).euclide' (so nn) nr (so q))
              (pair (so q) nn))
      (r (λ(nr:Bin).euclide' (nsz n) nr (nsz q))
         (λ(nr:Bin).euclide' (so n) nr (nsz q))
         (pair (nsz q) n))
  in euclide' end (reverse n) end


val div : Bin → Bin → Bin n m = pi1 (euclide n m)
val mod : Bin → Bin → Bin n m = pi2 (euclide n m)
*)

(* Printing in binary (High bit first)*)

val rec printb : Bin → {} = fun n →
  n (λnp. printb np; print("0")) (λnp. printb np; print("1")) {}

val printb : Bin → {} = fun n →
  printb n; print("\n")

(* Printing in decimal (quite slow)*)
val print_dec : Bin → {} = fun n → n
  (λnp.np (λnpp.npp (λx.print("8")) (λx.print("4")) print("?"))
          (λnpp.npp (λx.print("?")) (λx.print("6")) print("2")) print("?"))
  (λnp.np (λnpp.npp (λx.print("9")) (λx.print("5")) print("?"))
          (λnpp.npp (λx.print("?")) (λx.print("7")) print("3")) print("1"))
  print("0")

val print_dec : Bin → {} = fun n →
  print_dec n; print("\n")

(* fail termination
val rec print : Bin → {} = λn. (euclide n 10)
  (λq r. is_zero q {} (print q ; print_dec r))
*)

(* A classical example, that fail termination too
val rec fact = λn.is_zero n 1 (mul n (catch (pred n) fact 0))
*)

eval printb 100
