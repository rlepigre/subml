
include "nat.typ"
include "list.typ"

type STy(α) = μα Ty [ Atm of Nat | Arr of Ty × Ty ]
type Ty = STy(∞)

type STerm(α) = μα Term
  [ Var of Nat | App of Term × Term | Lam of Ty × Term ]

type Term = STerm(∞)

(*
type PSNeutral(α,S) = μα N
  [ Var of Nat | App of N × S ]

type SNormal(α,β) = μβ S [ Lam of Ty × S | Neu of PSNeutral(α,S) ]

type SNeutral(α,β) = PSNeutral(α+1,SNormal(α,β))

type Neutral = SNeutral(∞,∞)
type Normal = SNormal(∞,∞)

check Normal ⊂ Term
check Neutral ⊂ Normal
val test : ∀α∀β SNeutral(α,β) → SNormal(α,β+1) = λx. x
*)

val rec eq_type : Ty → Ty → Bool = fun t1 t2 →
  case t1 of
  | Atm n1 →
    (case t2 of
     | Atm n2 → eq n1 n2
     | Arr _ → fls)
  | Arr(t1',t1'') →
    (case t2 of
     | Atm _ → fls
     | Arr(t2',t2'') → and (eq_type t1' t2') (eq_type t1'' t2''))

val rec type_check : ∀α List(Ty) → STerm(α) → Option(Ty) = fun ctxt t →
  (case t of
  | Var n → nth ctxt n
  | Lam (t1, t) →
      (case type_check (t1::ctxt) t of
       | None → None
       | Some t2 → Some(Arr(t1,t2)))
  | App (t, u) →
      (case type_check ctxt u of
       | None → None
       | Some t1 →
        (case type_check ctxt t of
        | None → None
        | Some t2 →
         (case t2 of
          | Atm _ → abort
          | Arr(t1',tr) →
             if eq_type t1 t1' then Some(tr) else None))))


val test = type_check [] (Lam(Atm 0,Var 0))

eval test


val rec lift : ∀α STerm(α) → Nat → STerm(α) = fun t n →
  case t of
  | Lam(ty,t) →  Lam(ty, lift t (S n))
  | Var p → if geq p n then Var (S p) else t
  | App(t,u) → App(lift t n, lift u n)


val rec rebuild : ∀α Term → SList(α,Term) → Term = fun t l →
  case l of
  | [] → t
  | x::l → rebuild (App(t,x)) l

val none : Option(Term) = None

type Nat0 = [ H | Z | S of Nat ]

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

val rec subst : ∀α ∀β STerm(α) → STy(β) → Nat → Term → List(Term) → Option(Term) =
  fun t ty p u stack →
    (case t of
    | Var n →
    (case cmp p n of
    | H →
       (case u:Term of
        | Lam(_,t') →
            (case stack:List(Term) of
             | [] → Some u
             | v::stack →
               (case ty of
                | Atm _ → none
                | Arr(ty1,ty2) →
                  (case subst t' ty1 p v [] of
                   | None → none
                   | Some u → subst (Var Z) ty2 Z u stack)))
        | u → Some(rebuild u stack))
      | p → Some(rebuild (Var p) stack))
  | App(t1,t2) →
        (case subst t2 ty p u [] of
         | None → none
         | Some c →
            subst t1 ty p u (c::stack))
  | Lam(ty0, t) →
     (case stack of
      | [] →
        (case subst t ty (S p) (lift u Z) [] of
        | None → none
        | Some t → Some(Lam(ty0,t)))
      | _::_ → none))


val rec norm : Term → Option(Term) = fun t →
  (case t of
  | Lam(ty,t) →
     (case (norm t):Option(Term) of
      | None → none
      | Some t → Some((Lam(ty, t)):Term))
  | App(t1,t2) →
     (case (norm t2):Option(Term) of
      | None → none
      | Some v → (case (norm t1):Option(Term) of
         | None → none
         | Some w →
             (case w of
             | Lam(ty,t) → subst t ty Z v []
             | w → Some(App(w,v)))))
  | Var n → Some(Var n))

val deux : Term = Lam(Arr(Atm 0,Atm 0),Lam(Atm 0,App(Var 1,App(Var 1,Var 0))))
val nat : Ty = Arr(Arr(Atm 0,Atm 0),Arr(Atm 0,Atm 0))
val add : Term = Lam(nat,Lam(nat,Lam(Arr(Atm 0,Atm 0),Lam(Atm 0,
     App(App(Var 2,Var 1),App(App(Var 3,Var 1),Var 0))))))
eval type_check [] deux
eval type_check [] add

eval norm (App(App(add,deux),deux))