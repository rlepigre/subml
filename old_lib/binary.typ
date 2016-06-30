(* Binary coding of natural numbers, using Church encoding and typed *)

# boolean are needed
include "bool.typ";
include "prod.typ";
include "error.typ";

# recursive definition are used and this a typed file
recursive; typed; inductive;

type FBin(K) = ∀X((K → X) → (K → X) → X → X);
type Bin = !K FBin(K);

# Binary representation with lower bits first
let End : Bin = λz o e.e;        # end of the representation
let Sz  : Bin → Bin = λn z o e.z n; # adds a zero
let nSz  : Bin → Bin = λn.n (λnp z o e.z n) (λnp z o e.z n) End;
   # adds a zero and keep a normal representation
let So  : Bin → Bin = λn z o e.(o n);   # adds a one

# We will only use "normal" represention. This means we will assume
# that there is never some useless zeros at the end of a number.  To
# do this we need two functions which add a zero or a one in front of
# a normal representation, keeping it normal and caring about errors.

let eSz : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (Sz x));
let enSz : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (nSz x));
let eSo : Err(Bin) → Err(Bin)
  = λz. bind z (λx. unit (So x));

# Test for zero (works on non normal representation)
let rec Is_zero : Bin → Bool = λn.n
  (λnp.Is_zero np)
  (λnp.False)
  True
;

# Successor and zero
let Zero = End;
let rec S : Bin → Bin = λn.n (λnp.So np) (λnp.Sz (S np)) (So End);

# Predecessor
let rec Pred : Bin → Err(Bin) = λn.n
  (λnp.eSo (Pred np)) (λnp.unit (nSz np)) Error;

# Addition
let rec Add_aux : Bin → Bin → Bool → Bin
  = λn m r. n
  (λnp.m
    (λmp.r (So (Add_aux np mp False)) (Sz (Add_aux np mp False)))
    (λmp.r (Sz (Add_aux np mp True)) (So (Add_aux np mp False)))
    (r (So np) (Sz np)))
  (λnp.m
    (λmp.r (Sz (Add_aux np mp True)) (So (Add_aux np mp False)))
    (λmp.r (So (Add_aux np mp True)) (Sz (Add_aux np mp True)))
    (r (Sz (S np)) (So np)))
  (r (S m) m);
let Add = λn m.Add_aux n m False;

# Multiplication
let rec Mul : Bin → Bin → Bin = λn m.(n
  (λnp.Sz (Mul np m))
  (λnp.Add m (Sz (Mul np m)))
  End);

# Subtraction
let rec Sub_aux : Bin → Bin → Bool → Err(Bin) = λn m r. n
  (λnp.m
    (λmp.r (eSo (Sub_aux np mp True)) (enSz (Sub_aux np mp False)))
    (λmp.r (enSz (Sub_aux np mp True)) (eSo (Sub_aux np mp True)))
    (r (eSo (Pred np)) (unit (nSz np))))
  (λnp.m
    (λmp.r (enSz (Sub_aux np mp False)) (eSo (Sub_aux np mp False)))
    (λmp.r (eSo (Sub_aux np mp True)) (enSz (Sub_aux np mp False)))
    (r (unit (nSz np)) (unit (So np))))
  (r Error (Is_zero m (unit End) Error));
let Sub = λn m.Sub_aux n m False;


# Bad Division and modulo
let rec Euclide : Bin → Bin → Prod(Bin,Bin) = λn m. n
  (λnp. (Euclide np m (λq r.
      catch (Sub (nSz r) m)
        (λnr. pair (So q) nr)
        (pair (nSz q) (nSz r)))))
  (λnp. (Euclide np m (λq r.
      catch (Sub (So r) m)
        (λnr. pair (So q) nr)
        (pair (nSz q) (So r)))))
  (pair End End)
;

let Div : Bin → Bin → Bin n m = pi1 (Euclide n m);
let Mod : Bin → Bin → Bin n m = pi2 (Euclide n m);


# Another Division and modulo
let rec Reverse' : Bin → Bin → Bin = fun n a =>
  n (λnp.Reverse' np (Sz a)) (λnp.Reverse' np (So a)) a;
let Reverse n = Reverse' n End;

let Euclide n m =
  let rec Euclide' : Bin → Bin → Bin → Prod(Bin,Bin) n r q =
    catch (Sub n m)
      (λnn:Bin. r (λnr:Bin.Euclide' (nSz nn) nr (So q))
              (λnr:Bin.Euclide' (So nn) nr (So q))
              (pair (So q) nn))
      (r (λnr:Bin.Euclide' (nSz n) nr (nSz q))
         (λnr:Bin.Euclide' (So n) nr (nSz q))
         (pair (nSz q) n))
  in Euclide' End (Reverse n) End
;

let Div : Bin → Bin → Bin n m = pi1 (Euclide n m);
let Mod : Bin → Bin → Bin n m = pi2 (Euclide n m);

# Printing in binary (High bit first)
type Unit = ∀X (X → X);

let rec Printb : Bin → Unit n =
  n (λnp. Printb np "0") (λnp. Printb np "1") "";

# Printing in decimal (quite slow)
let Print_dec : Bin → Unit n = n
  (λnp.np (λnpp.npp (λx."8") (λx."4") "?")
          (λnpp.npp (λx."?") (λx."6") "2") "?")
  (λnp.np (λnpp.npp (λx."9") (λx."5") "?")
          (λnpp.npp (λx."?") (λx."7") "3") "1")
  "0"
;
let dix : Bin = λz o e.z (λz o e.o (λz o e.z (λz o e.o (λz o e.e))));
let rec Print : Bin → Unit = λn. (Euclide n dix)
  (λq r. Is_zero q "" (Print q) (Print_dec r));


# Some numbers
let 0 = End;
let 1 = S 0;
let 2 = S 1;
let 3 = S 2;
let 4 = S 3;
let 5 = S 4;
let 6 = S 5;
let 7 = S 6;
let 8 = S 7;
let 9 = S 8;
let 10 = S 9;
let 20 = Add 10 10;
let 30 = Add 20 10;
let 40 = Add 30 10;
let 100 = Mul 10 10;

# A classical example:
let rec Fact = λn.Is_zero n 1 (Mul n (catch (Pred n) Fact 0));
