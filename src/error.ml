(****************************************************************************)
(**{3         Functions collecting error annotations in prooftree          }*)
(****************************************************************************)

open Print
open Ast
open Format

type error =
  | Typ of ordi list * term * kind
  | Sub of ordi list * term * kind * kind
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

let rec check_sub_proof (p, t, k1, k2, r) =
  let res =
    match r with
    | Sub_Delay { contents = p }
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
    | Sub_Or_r   p
    | Sub_Gen(_,_,p)       -> check_sub_proof p
    | Sub_Func   (p1, p2) -> check_sub_proof p1 &&& check_sub_proof p2
    | Sub_Prod   ps
    | Sub_DSum   ps       -> for_all (fun (l,p) -> check_sub_proof p) ps
    | Sub_Lower
    | Sub_Ind _           -> None
    | Sub_Error msg       -> Some [ Msg msg ]
  in
  match res with
  | None -> None
  | Some l -> Some (Sub(p,t,k1,k2) :: l)

and check_typ_proof (p, t, k, r) =
  let rec fn ptr = match !ptr with
    | Todo -> Some [ Msg "Cannot find inductive hypothesis" ]
    | Induction(_,p) -> check_sub_proof p
    | Unroll(_,_,p) -> check_typ_proof p
  in
  let res =
    match r with
    | Typ_YGen ptr -> fn ptr
    | Typ_Coer   (p2, p1)
    | Typ_Func_i (p2, p1)
    | Typ_DSum_i (p2, p1) -> check_typ_proof p1 &&& check_sub_proof p2

    | Typ_Nope   p
    | Typ_Yufl   p
    | Typ_Prod_e p        -> check_typ_proof p

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
    | Typ_Abrt            -> None
    | Typ_Error msg       -> Some [ Msg msg ]
  in
  match res with
  | None -> None
  | Some l -> Some (Typ(p,t,k) :: l)

let check_sub_proof p =
  match check_sub_proof p with
  | None -> ()
  | Some l -> raise (Error l)

let check_typ_proof p =
  match check_typ_proof p with
  | None -> ()
  | Some l -> raise (Error l)

let display_error ch = function
  | Typ(p,t,k)     -> fprintf ch "TYP %a ⊢ %a : %a\n" print_ordis p
                              (print_term ~give_pos:true false) t
                              (print_kind false) k
  | Sub(p,t,k1,k2) -> fprintf ch "SUB %a ⊢ %a ⊂ %a\n"
                              print_ordis p
                              (print_kind false) k1
                              (print_kind false) k2
  | Msg(m)       -> fprintf ch "MSG %s" m

let display_errors ch = List.iter (display_error ch)
