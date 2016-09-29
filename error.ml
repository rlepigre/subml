open Ast
open Format

type error =
  | Typ of term * kind
  | Sub of term * kind * kind
  | Msg of string

type errors = error list

exception Error of errors

let (&&&) p1 p2 = match p1, p2 with
  | None, None -> None
  | Some p1, _ -> Some p1
  | _, Some p2 -> Some p2

let rec for_all f = function
  | [] -> None
  | x::l -> f x &&& for_all f l

let rec check_sub_proof (t, k1, k2, _, r) =
  let res =
    match r with
    | Sub_Delay { contents = p }
    | Sub_With_l p
    | Sub_With_r p
    | Sub_KAll_r p
    | Sub_KAll_l p
    | Sub_KExi_l p
    | Sub_KExi_r p
    | Sub_OAll_r p
    | Sub_OAll_l p
    | Sub_OExi_l p
    | Sub_OExi_r p
    | Sub_FixM_r p
    | Sub_FixN_l p
    | Sub_FixM_l p
    | Sub_FixN_r p
    | Sub_And_l  p
    | Sub_And_r  p
    | Sub_Or_l   p
    | Sub_Or_r   p        -> check_sub_proof p
    | Sub_Func   (p1, p2) -> check_sub_proof p1 &&& check_sub_proof p2
    | Sub_Prod   ps
    | Sub_DSum   ps       -> for_all check_sub_proof ps
    | Sub_DPrj_r (p1, p2)
    | Sub_DPrj_l (p1, p2) -> check_typ_proof p1 &&& check_sub_proof p2
    | Sub_Lower
    | Sub_Ind _           -> None
    | Sub_Error msg       -> Some [ Msg msg ]
  in
  match res with
  | None -> None
  | Some l -> Some (Sub(t,k1,k2) :: l)

and check_typ_proof (t, k, r) =
  let res =
    match r with
    | Typ_Coer   (p2, p1)
    | Typ_Func_i (p2, p1)
    | Typ_DSum_i (p2, p1) -> check_typ_proof p1 &&& check_sub_proof p2

    | Typ_KAbs   p
    | Typ_OAbs   p
    | Typ_TFix (_, { contents = p })
    | Typ_Prod_e p        -> check_typ_proof p

    | Typ_YH (_, p)
    | Typ_Defi   p
    | Typ_Prnt   p
    | Typ_Cnst   p        -> check_sub_proof p

    | Typ_Func_e (p1, p2) -> check_typ_proof p1 &&& check_typ_proof p2

    | Typ_Prod_i (p, ps)  -> check_sub_proof p &&& for_all check_typ_proof ps
    | Typ_DSum_e (p, ps, None)
                          -> check_typ_proof p &&& for_all check_typ_proof ps
    | Typ_DSum_e (p, ps, Some po)
                          -> check_typ_proof p &&& for_all check_typ_proof ps &&&
                             check_typ_proof po

    | Typ_Hole            -> None
    | Typ_Error msg       -> Some [ Msg msg ]
  in
  match res with
  | None -> None
  | Some l -> Some (Typ(t,k) :: l)

let check_sub_proof p =
  match check_sub_proof p with
  | None -> ()
  | Some l -> raise (Error l)

let check_typ_proof p =
  match check_typ_proof p with
  | None -> ()
  | Some l -> raise (Error l)

let display_error ch = function
  | Typ(t,k)     -> printf "TYP %a : %a\n" (!fprint_term false) t (!fprint_kind false) k
  | Sub(t,k1,k2) -> printf "SUB %a ⊂ %a\n" (!fprint_kind false) k1 (!fprint_kind false) k2
  | Msg(m)       -> printf "MSG %s" m

let display_errors ch = List.iter (display_error ch)
