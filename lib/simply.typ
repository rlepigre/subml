include "nat.typ"
include "list.typ"

type STy(α) = μα T.[Atm of Nat | Arr of T × T]
type Ty = STy(∞)

type FTerm(A) = [Var of Nat | App of A × A | Lam of Ty × A]
type STerm(α) = μα T.FTerm(T)
(** STerm(α) means F(F(...F(∀X.X))) α times *)
type Term = STerm(∞)
(** Term = FTerm(Term) *)

(** Equality on types *)
val rec eq_type : Ty → Ty → Bool = fun t1 t2 →
  case t1 of
  | Atm n1 →
    (case t2 of
     | Atm n2 → eq n1 n2
     | Arr _ → Fls)
  | Arr(t1',t1'') →
    (case t2 of
     | Atm _ → Fls
     | Arr(t2',t2'') → and (eq_type t1' t2') (eq_type t1'' t2''))

(** Type inference function *)
val rec type_infer : ∀α.List(Ty) → STerm(α) → Option(Ty) = fun ctxt t →
  (case t of
  | Var n → nth ctxt n
  | Lam (t1, t) →
      (case type_infer (t1::ctxt) t of
       | None → None
       | Some t2 → Some(Arr(t1,t2)))
  | App (t, u) →
      (case type_infer ctxt u of
       | None → None
       | Some t1 →
        (case type_infer ctxt t of
        | None → None
        | Some t2 →
         (case t2 of
          | Atm _ → abort
          | Arr(t1',tr) →
             if eq_type t1 t1' then Some(tr) else None))))


val test = type_infer [] (Lam(Atm 0,Var 0))

eval test

(** Lifting of Free Debrujn variable by one *)
val rec lift : ∀α.STerm(α) → Nat → STerm(α) = fun t n →
  case t of
  | Lam(ty,t) →  Lam(ty, lift t (S n))
  | Var p → if geq p n then Var (S p) else t
  | App(t,u) → App(lift t n, lift u n)

(** napp a sequence of applications from a list *)
val rec napp : ∀α.Term → SList(α,Term) → Term = fun t l →
  case l of
  | [] → t
  | x::l → napp (App(t,x)) l

type Nat0 = [ H | Z | S of Nat ]

(** cmp n m return →
   H if n = m
   m if m < n (variable below the substitude variable)
   m-1 if m > n (free variable needs to decrease by one)
*)
val rec cmp : Nat → Nat → Nat0 = fun n m →
  case n of
  | Z →
     (case m of
     | Z → H
     | S m' → m')
  | S n' →
     (case m of
     | Z → Z
     | S m' → (case cmp n' m' of H → H | n → S n))

(** subst t ty v u stack:
   - t, u and the term in the stack must all be normal
   - substitute the variable v by u in t and applies the result
     to the stack and normalises it.
   - ty must be the type of v and u

   - abort if untyped of if the argument are not normal
   - termininates by lex order (|ty|,|t|), this is R David proofs
     when the terms are not normal as they should.
*)
val rec subst : ∀α.∀β.STerm(α) → STy(β) → Nat → Term → List(Term) → Term =
  fun t ty p u stack →
    (case t of
    | Var n →
      (case cmp p n of
      | H →
         (case (u:Term) of
         | Lam(_,t') →
            (case (stack:List(Term)) of
             | [] → u
             | v::stack →
                (case ty of
                | Atm _ → print("untyped\n"); abort
                | Arr(ty1,ty2) →
                  let t'' = subst t' ty1 Z v [] in
                  subst (Var Z) ty2 Z t'' stack))
        | u → napp u stack)
      | p → napp (Var p) stack)
  | App(t1,t2) →
        let t2' = subst t2 ty p u [] in
        subst t1 ty p u (t2'::stack)
  | Lam(ty0, t) →
     (case stack of
      | [] →
        let t' = subst t ty (S p) (lift u Z) [] in
        Lam(ty0,t')
      | _::_ → print("not normal in subst\n"); abort))

(** normalisation is easy using subst *)
val rec[1] norm : Term → Term = fun t →
  (case t of
  | App(t1,t2) →
     (let t2' = norm t2 in
     let t1' = norm t1 in
     case t1' of
       | Lam(ty,t) → subst t ty Z t2' []
       | App(j,k) → App(App(j,k),t2')
       | Var(k) → App(Var(k),t2'))
  | Lam(ty,t) → Lam(ty, norm t)
  | Var n → Var n)

(** testing *)
val deux : Term = Lam(Arr(Atm 0,Atm 0),Lam(Atm 0,App(Var 1,App(Var 1,Var 0))))
val nat : Ty = Arr(Arr(Atm 0,Atm 0),Arr(Atm 0,Atm 0))
val add : Term = Lam(nat,Lam(nat,Lam(Arr(Atm 0,Atm 0),Lam(Atm 0,
     App(App(Var 2,Var 1),App(App(Var 3,Var 1),Var 0))))))
val mul : Term = Lam(nat,Lam(nat,Lam(Arr(Atm 0,Atm 0),
     App(Var 1, App(Var 2, Var 0)))))

eval type_infer [] deux
eval type_infer [] add
eval type_infer [] mul

val quatre : Term = App(App(add,deux),deux)
val seize : Term = App(App(mul,quatre),quatre)

eval norm deux
eval norm quatre
eval norm seize
