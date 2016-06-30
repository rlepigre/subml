open Ast
open Print
open Latex
open Bindlib

type latex_output =
  | Kind    of int * bool * kind
  | KindDef of int * type_def
  | Term    of int * bool * term
  | Text    of string
  | List    of latex_output list
  | SProof  of sub_prf * Sct.calls_graph
  | TProof  of typ_prf
  | Sct     of Sct.calls_graph
  | Witnesses

let rec to_string = function
  | Text(t) -> t
  | List(l) -> "{" ^ String.concat "" (List.map to_string l) ^"}"
  | _       -> assert false

let print_calls ch arities calls =
  let print_cmp ch c =
    match c with
    | Sct.Unknown -> Printf.fprintf ch "?"
    | Sct.Less    -> Printf.fprintf ch "<"
    | Sct.Leq     -> Printf.fprintf ch "="
  in
  let print_args ch i =
    let a = try List.assoc i arities with Not_found -> assert false in
    for i = 0 to a - 1 do
      Printf.fprintf ch "%sx_%d" (if i = 0 then "" else ",") i
    done
  in
  Printf.fprintf ch "\\begin{dot2tex}[dot,options=-tmath]\n  digraph G {\n";
  List.iter (fun (i,_) ->
    Printf.fprintf ch "    N%d [ label = \"I_%d(%a)\" ];\n" i i print_args i) (List.filter (fun (i,_) ->
       List.exists (fun (j,k,_) -> i = j || i =k) calls) arities);
  let print_call arities (i,j,m) =
    Printf.fprintf ch "    N%d -> N%d [label = \"(" j i;
    Array.iteri (fun i l ->
      if i > 0 then Printf.fprintf ch ",";
      let some = ref false in
      Array.iteri (fun j c ->
	if c <> Sct.Unknown then (
	  let sep = if !some then " " else "" in
	  Printf.fprintf ch "%s%aX%d" sep print_cmp c j;
	  some := true
	)) l;
      if not !some then Printf.fprintf ch "?") m;
    Printf.fprintf ch ")\"]\n%!"
  in
  List.iter (print_call arities) calls;
  Printf.fprintf ch "  }\n\\end{dot2tex}\n"

let rec typ2proof : typ_prf -> string Proof.proof = fun (t,k,r) ->
  let open Proof in
  let t2s = term_to_string false and k2s = kind_to_string false in
  let c = Printf.sprintf "$%s : %s$" (t2s t) (k2s k) in
  match r with
  | Typ_Coer(p1,p2)   -> binaryN "$\\subset$" c (sub2proof p1) (typ2proof p2)
  | Typ_KAbs(p)       -> unaryN "$\\Lambda$" c (typ2proof p)
  | Typ_OAbs(p)       -> unaryN "$\\Lambda_o$" c (typ2proof p)
  | Typ_Defi(p)       -> assert false (* TODO *)
  | Typ_Prnt(p)       -> unaryN "$print$" c (sub2proof p)
  | Typ_Cnst(p)       -> unaryN "$=$" c (sub2proof p)
  | Typ_Func_i(p1,p2) -> binaryN "$\\to_i$" c (sub2proof p1) (typ2proof p2)
  | Typ_Func_e(p1,p2) -> binaryN "$\\to_i$" c (typ2proof p1) (typ2proof p2)
  | Typ_Prod_i(p,ps)  -> n_aryN "$\\times_i$" c
                           (sub2proof p :: List.map typ2proof ps)
  | Typ_Prod_e(p)     -> unaryN "$\\times_e$" c (typ2proof p)
  | Typ_DSum_i(p1,p2) -> binaryN "$+_i$" c (sub2proof p1) (typ2proof p2)
  | Typ_DSum_e(p,ps)  -> n_aryN "$+_e$" c
                           (typ2proof p :: List.map typ2proof ps)
  | Typ_YH(n,p)          ->
     let name = Printf.sprintf "$H_%d$" n in
     unaryN name c (sub2proof p)
  | Typ_Y(n,p1,p2,p)     ->
     let name = Printf.sprintf "$I_%d$" n in
     ternaryN name c (sub2proof p1) (sub2proof p2) (typ2proof p)

and     sub2proof : sub_prf -> string Proof.proof = fun (t,a,b,ir,r) ->
  let open Proof in
  let t2s = term_to_string false and k2s = kind_to_string false in
  let c = Printf.sprintf "$%s \\in %s \\subset %s$" (t2s t) (k2s a) (k2s b) in
  match r with
  | Sub_Delay(pr)     -> sub2proof !pr
  | Sub_Lower         -> hyp (Printf.sprintf "$%s \\leq %s$" (k2s a) (k2s b))
  | Sub_Func(p1,p2)   -> binaryN "$\\to$" c (sub2proof p1) (sub2proof p2)
  | Sub_Prod(ps)      -> n_aryN "$\\times$" c (List.map sub2proof ps)
  | Sub_DSum(ps)      -> n_aryN "$+$" c (List.map sub2proof ps)
  | Sub_DPrj_l(p1,p2) -> binaryN "$\\pi_l$" c (typ2proof p1) (sub2proof p2)
  | Sub_DPrj_r(p1,p2) -> binaryN "$\\pi_r$" c (typ2proof p1) (sub2proof p2)
  | Sub_With_l(p)     -> unaryN "$w_l$" c (sub2proof p)
  | Sub_With_r(p)     -> unaryN "$w_r$" c (sub2proof p)
  | Sub_KAll_r(p)     -> unaryN "$\\forall_r$" c (sub2proof p)
  | Sub_KAll_l(p)     -> unaryN "$\\forall_l$" c (sub2proof p)
  | Sub_KExi_l(p)     -> unaryN "$\\exists_l$" c (sub2proof p)
  | Sub_KExi_r(p)     -> unaryN "$\\exists_r$" c (sub2proof p)
  | Sub_OAll_r(p)     -> unaryN "$\\forall_{or}$" c (sub2proof p)
  | Sub_OAll_l(p)     -> unaryN "$\\forall_{ol}$" c (sub2proof p)
  | Sub_OExi_l(p)     -> unaryN "$\\exists_{ol}$" c (sub2proof p)
  | Sub_OExi_r(p)     -> unaryN "$\\exists_{or}$" c (sub2proof p)
  | Sub_FixM_r(p)     -> unaryN "$\\mu_r$" c (sub2proof p)
  | Sub_FixN_l(p)     -> unaryN "$\\nu_l$" c (sub2proof p)
  | Sub_FixM_l(p)     -> unaryN "$\\mu_l$" c (sub2proof p)
  | Sub_FixN_r(p)     -> unaryN "$\\nu_r$" c (sub2proof p)
  | Sub_Ind(n)        -> hyp (Printf.sprintf "$H_%d" n)
  | Sub_Dummy         -> assert false (* Should not happen. *)

let print_typing_proof    ch p = Proof.output ch (typ2proof p)
let print_subtyping_proof ch p = Proof.output ch (sub2proof p)

let rec output ch = function
  | Kind(n,unfold,k) -> break_hint := n; print_kind unfold ch k; break_hint := 0
  | Term(n,unfold,t) -> break_hint := n; print_term unfold ch t; break_hint := 0
  | Text(t)        -> Printf.fprintf ch "%s" t
  | List(l)        -> Printf.fprintf ch "{%a}" (fun ch -> List.iter (output ch)) l
  (*
  | SProof (p,(tt,sct)) ->
     Printf.fprintf ch "\\begin{prooftree}\n";
     print_subtyping_proof ch p;
     Printf.fprintf ch "\\end{prooftree}\n%!";
     Printf.fprintf ch "\\begin{center}\n";
     if sct <> [] then print_calls ch tt sct;
     Printf.fprintf ch "\\end{center}\n%!";
     *)
  | TProof p       -> print_typing_proof ch p
  | Witnesses      -> print_epsilon_tbls ch; reset_epsilon_tbls ()
  | KindDef(n,t)     ->
     let name = t.tdef_tex_name in
     let f = t.tdef_value in
     let args = mbinder_names f in
     let params = Array.map (fun s -> free_of (new_kvari s)) args in
     let k = msubst f params in
     let print_array cg a =
       if Array.length a = 0 then () else
       Printf.fprintf ch "(%s%a)" a.(0) (fun ch a ->
         for i = 1 to Array.length a - 1 do
           Printf.fprintf ch ",%s" a.(i)
         done) a
     in
     break_hint := n;
     Printf.fprintf ch "%s%a &= %a" name print_array args (print_kind true) k;
     break_hint := 0
  | Sct (arities,calls) ->
      print_calls ch arities calls
