open Bindlib
open Util
open Ast
open Print
open Trace
open Sct

let debug = ref false

exception Type_error of pos * string
exception Subtype_error of string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype_error : string -> 'a = fun msg ->
  raise (Subtype_error msg)

type branch_element =
  | Judgment of kind * kind
  | BSum of string
  | BProd of string
  | BArrow of bool

type subtype_ctxt = (kind * kind * int * ordinal array * (unit -> unit)) list * calls ref

exception Found of cmp * int

let find_index a o =
  try
    Array.iteri (fun i o' -> if less_ordinal o o' then raise (Found(Less,i))
      else if leq_ordinal o o' then raise (Found(Leq,i))) a;
    assert false
  with Found(c,i) -> (c, i)

let find_indexes a b =
  let indexes = Array.make (Array.length a) 0 in
  let cmps = Array.mapi (fun i o -> let (c,j) = find_index b o in indexes.(i) <- j; c) a in
  cmps, indexes

let try_inline ctxt num =
  let calls = snd ctxt in
  let count, call = List.fold_left (
    fun (n,_ as acc) (i,j,c,a as call) ->
      if i = num then (n + 1, Some call) else acc) (0,None) !calls in
  match count, call with
  | 1, Some(_,j,c,a) -> (* one use: do inlining *)
     calls := List.filter (fun (i,_,_,_) -> i <> num) !calls;
     calls := List.map (fun (i,k,c',a' as call) ->
       if k = num then
	 let c'',a'' = compose c' a' c a in
	 (i,j,c'',a'') else call) !calls
  | _ -> ()


exception Induction_hypothesis

(****************************************************************************
 *                                 Lower kind                               *
****************************************************************************)

let search k l =
  let rec fn acc = function
    | []        -> raise Not_found
    | (x,l)::xs when eq_kind k x -> (acc, l, xs)
    | (x,l)::xs -> fn ((x,l)::acc) xs
  in fn [] l


let lower_kind k1 k2 =
  let i = ref 0 in
  let new_int () = incr i; TInt !i in
  let rec lower_kind k1 k2 =
    if !debug then Printf.eprintf "    %a ≤ %a\n%!" (print_kind false) k1 (print_kind false) k2;
    match (repr k1, repr k2) with
    | (k1          , k2          ) when k1 == k2 -> true
    | (TVar(_)     , TVar(_)     ) -> assert false
    | (Func(a1,b1) , Func(a2,b2) ) -> lower_kind a2 a1 && lower_kind b1 b2
    | (DSum(fsa)   , DSum(fsb)   )
    | (Prod(fsa)   , Prod(fsb)   ) ->
       let cmp (k1,_) (k2,_) = compare k1 k2 in
       let f (la,a) (lb,b) = la = lb && lower_kind a b in
       List.length fsa = List.length fsb &&
           List.for_all2 f (List.sort cmp fsa) (List.sort cmp fsb)
    | (FAll(a)     , FAll(b)     ) ->
       let i = new_int () in
       lower_kind (subst a i) (subst b i)
    | (Exis(a)     , FAll(b)     ) ->
       let i = new_int () in
       lower_kind (subst a i) (subst b i)
    | (FixM(oa,fa) , FixM(ob,fb) ) ->
       leq_ordinal oa ob && (fa == fb ||
			       let i = new_int () in lower_kind (subst fa i) (subst fb i))
    | (FixN(oa,fa) , FixN(ob,fb) ) ->
       leq_ordinal ob oa && (fa == fb ||
			       let i = new_int () in lower_kind (subst fa i) (subst fb i))
    | (TDef(da,aa) , TDef(db,ab) ) ->
       lower_kind (msubst da.tdef_value aa) (msubst db.tdef_value ab)
    | (UCst(ca)    , UCst(cb)    ) ->
       let i = new_int () in
       let a = subst ca.qcst_wit_kind i in
       let b = subst cb.qcst_wit_kind i in
       lower_kind a b && ca.qcst_wit_term == cb.qcst_wit_term
      (* FIXME what of the bound ? *)
    | (ECst(ca)    , ECst(cb)    ) ->
       let i = new_int () in
       let a = subst ca.qcst_wit_kind i in
       let b = subst cb.qcst_wit_kind i in
       lower_kind a b && ca.qcst_wit_term == cb.qcst_wit_term
      (* FIXME what of the bound ? *)
    | (UVar(ua)    , UVar(ub)    ) when ua == ub -> true
    | (TInt(ia)    , TInt(ib)    ) -> ia = ib
    | (_           , _           ) -> false
  in lower_kind k1 k2

let cr = ref 0

let check_rec : term -> subtype_ctxt -> kind -> kind -> subtype_ctxt * kind * kind * int option =
  fun t ctxt a b ->
    match (a, b) with
    | (FixM _, _) | (FixN _, _) | (_, FixM _) | (_, FixN _) ->
       let (a', os1) = decompose false a in
       let (b', os2) = decompose true b in
       let os' = os1 @ os2 in
       let os' = Array.of_list os' in
       let os1 = List.map (fun o ->
	 incr cr;
	 OLEqu(o,dummy_pos (TagI !cr),In(binder_from_fun "a" 0 (fun o -> a')))) os1 in (* FIXME *)
       let os2 = List.map (fun o ->
	 incr cr;
	 OLEqu(o,dummy_pos (TagI !cr),In(binder_from_fun "a" 0 (fun o -> b')))) os2 in (* FIXME *)
       let los = os1 @ os2 in
       let os = Array.of_list los in
       let fnum = new_function (Array.length os) in
       begin match ctxt with
	 [], _ -> ()
       | (_,_,cur,os0,_)::_ as up, calls  ->
	  List.iter (fun (a0,b0,index,_,use) ->
	    if eq_kind a0 a' && eq_kind b0 b' then (
	      let cmp, ind = find_indexes os' os0 in
	      calls := (index, cur, cmp, ind) :: !calls;
	      use ();
	      let _ = trace_subtyping t a b in
	      trace_sub_pop (NUseInd index);
	      raise Induction_hypothesis)) up;
	 let cmp, ind = find_indexes os os0 in
	 calls := (fnum, cur, cmp, ind)::!calls;
       end;
       let use = trace_subtyping ~ordinal:los t a b in
       let a = recompose false a' os1 in
       let b = recompose true b' os2 in
       let ctxt = (a', b', fnum, os,use)::fst ctxt, snd ctxt in
       (ctxt, a, b, Some fnum)
    | _ ->
       (ctxt, a, b, None)

let subtype : term -> kind -> kind -> unit = fun t a b ->
  let rec subtype ctxt t a b =
    let a = repr a in
    let b = repr b in
    if !debug then Printf.eprintf "%a ⊂ %a (∋ %a)\n%!" (print_kind false) a (print_kind false) b (print_term false) t;
    (try
       if a == b || lower_kind a b then
         let _ = trace_subtyping t a b in
	 trace_sub_pop NRefl
       else
    begin match (a,b) with
    (* Handling of unification variables (immitation). *)
    | (UVar ua, UVar ub) ->
       let _ = trace_subtyping t a b in
       trace_sub_pop NRefl;
       if ua == ub then () else set ua b;
    | (UVar ua, _      ) ->
        let k =
          match uvar_occur ua b with
          | Non -> b
	  | Pos -> FixM(OConv,bind_uvar ua b)
          | _   -> bot
        in
	if !debug then Printf.eprintf "  set %a <- %a\n%!" (print_kind false) a (print_kind false) k;
	let _ = trace_subtyping t a b in
	trace_sub_pop NRefl;
        set ua k
    | (_      , UVar ub) ->
        let k =
          match uvar_occur ub a with
          | Non -> a
	  | Pos -> FixM(OConv,bind_uvar ub a)
          | _   -> top
        in
	if !debug then Printf.eprintf "  set %a <- %a\n%!" (print_kind false) b (print_kind false) k;
	let _ = trace_subtyping t a b in
	trace_sub_pop NRefl;
        set ub k

    (* Type definition. *)
    | (TDef(d,a)  , _          ) ->
        subtype ctxt t (msubst d.tdef_value a) b

    | (_          , TDef(d,b)  ) ->
        subtype ctxt t a (msubst d.tdef_value b)

    | _ ->
    let (ctxt, a, b, cmps) = check_rec t ctxt a b in
    let _ = trace_subtyping t a b in
    begin match (a,b) with
    (* Arrow type. *)
    | (Func(a1,b1), Func(a2,b2)) ->
        let f x = appl dummy_position (box t) x in
        let bnd = unbox (bind (lvar_p dummy_position) "x" f) in
        let wit = cnst bnd a2 b2 in
        subtype ctxt (dummy_pos (Appl(t,wit))) b1 b2;
        subtype ctxt wit a2 a1;
	trace_sub_pop NArrow

    (* Product type. *)
    | (Prod(fsa), Prod(fsb)) ->
        let check_field (l,b) =
          let a = try List.assoc l fsa with Not_found -> subtype_error "Product fields clash." in
          subtype ctxt (dummy_pos (Proj(t,l))) a b
        in
        List.iter check_field fsb;
	trace_sub_pop NProd

    (* Sum type. *)
    | (DSum([]), a)          -> trace_sub_pop NSum

    | (DSum(csa), DSum(csb)) ->
        let check_variant (c,a) =
          let t = unbox
            (case dummy_position (box t) [(c, idt)])
          in
	  try
            let b = List.assoc c csb in
            subtype ctxt t a b
	  with
	    Not_found -> subtype ctxt t a (DSum([]))
        in
        List.iter check_variant csa;
	trace_sub_pop NSum

    (* Universal quantifier. *)
    | (_        , FAll(f)  ) ->
       let b' = subst f (new_ucst t f) in
       subtype ctxt t a b';
       trace_sub_pop NAllRight

    | (FAll(f)  , _        ) ->
        subtype ctxt t (subst f (new_uvar ())) b;
      trace_sub_pop NAllLeft

    (* Existantial quantifier. *)
    | (Exis(f)  , _        ) ->
       let a' = subst f (new_ecst t f) in
       subtype ctxt t a' b;
       trace_sub_pop NExistsLeft

    | (_        , Exis(f)  ) ->
       subtype ctxt t a (subst f (new_uvar ()));
       trace_sub_pop NExistsRight

     (* μ and ν - least and greatest fixpoint. *)
    | (_          , FixN(o,f)) ->
       let o' = OLess(o, t, NotIn(binder_from_fun "a" 0 (fun o -> FixN(o, f)))) in
       if !debug then Printf.eprintf "creating %a < %a\n%!" print_ordinal o' print_ordinal o;
       let cst = FixN(o', f) in
       subtype ctxt t a (subst f cst);
       trace_sub_pop NNuRight

    | (FixM(o,f)  , _        ) ->
       let o' = OLess(o, t, In(binder_from_fun "a" 0 (fun o -> FixM(o, f)))) in
       if !debug then Printf.eprintf "creating %a < %a\n%!" print_ordinal o' print_ordinal o;
       let cst = FixM(o', f) in
       subtype ctxt t (subst f cst) b;
       trace_sub_pop NMuLeft

    | (FixN(OConv,f)  , _        ) ->
       subtype ctxt t (subst f a) b;
       trace_sub_pop NNuLeft

    | (_          , FixM(OConv,f)) ->
       subtype ctxt t a (subst f b);
      trace_sub_pop NMuRight

    (* Subtype clash. *)
    | (_, _) -> subtype_error "Subtyping clash (no rule apply)."
    end;
    (match cmps with
    | None -> ()
    | Some call_num ->
       try_inline ctxt call_num;
       trace_sub_pop (NInd call_num));
    end;
    with Induction_hypothesis -> ());
  in
  let calls = ref [] in
  subtype ([],calls) t a b;
  (*  print_calls Format.std_formatter !calls;*)
  if not (sct !calls)  then subtype_error "loop"

let generic_subtype : kind -> kind -> unit = fun a b ->
  subtype (generic_cnst a b) a b

let type_check : term -> kind -> unit = fun t c ->
  let c = repr c in
  let rec type_check t c =
    if !debug then Printf.eprintf "%a : %a\n%!" (print_term false) t (print_kind false) c;
    trace_typing t c;
    (match t.elt with
    | Coer(t,a) ->
        subtype t a c;
        type_check t a
    | LVar(x) ->
        type_error t.pos "Cannot type-check open terms..."
    | LAbs(ao,f) ->
        let a = match ao with None -> new_uvar () | Some a -> a in
        let b = new_uvar () in
        subtype t (Func(a,b)) c;
        type_check (subst f (cnst f a b)) b
    | Appl(t,u) ->
        let a = new_uvar () in
        type_check t (Func(a,c));
        type_check u a
    | Reco(fs) ->
        let ts = List.map (fun (l,_) -> (l, new_uvar ())) fs in
        subtype t (Prod(ts)) c;
        let check (l,t) =
          let cl = List.assoc l ts in
          type_check t cl
        in
        List.iter check fs
    | Proj(t,l) ->
        let c' = Prod([(l,c)]) in
        type_check t c'
    | Cons(d,v) ->
        let a = new_uvar () in
        let c' = DSum([(d,a)]) in
        type_check v a;
        subtype t c' c
    | Case(t,l) ->
       let ts = List.map (fun (c,_) -> (c, new_uvar ())) l in
        type_check t (DSum(ts));
        let check (d,f) =
          let cc = List.assoc d ts in
          type_check f (Func(cc,c))
        in
        List.iter check l
    | VDef(v) ->
        subtype v.value v.ttype c
    | Prnt(_) ->
       subtype t (Prod []) c
    | FixY(t) ->
       type_check t (Func(c,c))
    | Cnst(cst) ->
        let (_,a,_) = cst in
        subtype t a c
    | TagI(_) ->
       assert false (* Cannot happen. *));
    trace_typ_pop ();
  in
  type_check t c
