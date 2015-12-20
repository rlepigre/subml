open Bindlib
open Util
open Ast
open Print
open Trace

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

type subtype_ctxt =
  { lfix : (kind * (ordinal * kind * (unit -> unit)) list) list
  ; rfix : (kind * (ordinal * kind * (unit -> unit)) list) list
  ; adone : branch_element list }

let find_repetition a b branch =
  let rec fn acc = function
    | [] -> false
    | Judgment(a',b')::l when eq_kind a a' && eq_kind b b' -> (gn (List.rev acc) l || fn acc l)
    | Judgment _ :: l -> fn acc l
    | x::l -> fn (x::acc) l
  and gn l1 l2 = match l1, l2 with
    | [], Judgment(a',b') :: _ when eq_kind a a' && eq_kind b b' -> true
    | l1, Judgment _ :: l2 -> gn l1 l2
    | Judgment _ :: l1, _ -> assert false
    | (x::l1), (y::l2) when x = y -> gn l1 l2
    | _ -> false
  in fn [] branch

exception Induction_hypothesis

let struct_eq k1 k2 =
  let k1, os1 = decompose k1 in
  let k2, os2 = decompose k2 in
  eq_kind k1 k2

let add_left_ind_hyp ctxt k1 k2 =
(* if the is an induction hyp k2 < k3 and k1 < k2, add k1 < k3 as ind. hyp. *)
  let add l =
    List.fold_right (fun (o,k2',f as tpl) acc ->
      if lower_kind k2 k2' then tpl::(o,k1,f)::acc else tpl::acc) l []
  in
  { ctxt with rfix = List.map (fun (k,l) -> (k, add l)) ctxt.rfix }

let add_right_ind_hyp ctxt k1 k2 =
  (* if the is an induction hyp k3 < k2 and k2 < k1, add k3 < k1 as ind. hyp. *)
  let add l =
    List.fold_right (fun (o,k2',f as tpl) acc ->
      if lower_kind k2' k2 then tpl::(o,k1,f)::acc else tpl::acc) l []
  in
  { ctxt with lfix = List.map (fun (k,l) -> (k, add l)) ctxt.lfix }


let check_rec : term -> subtype_ctxt -> kind -> kind -> subtype_ctxt * kind * kind =
  fun t ctxt a b ->
    let search k l =
      let rec fn acc = function
        | []        -> raise Not_found
        | (x,l)::xs when eq_kind k x -> (acc, l, xs)
        | (x,l)::xs -> fn ((x,l)::acc) xs
      in fn [] l
    in

    (* Check left. *)
    begin match a with
      | FixM(o,f) ->
         begin
	   try
	     let key = FixM(ODumm,f) in
	     let (before, l, after) = search key ctxt.lfix in
             let check (o', k, used) =
               if less_ordinal o o' && lower_kind k b then
		 (used ();
		  if !debug then Printf.eprintf "Induction applies\n%!";
		  raise Induction_hypothesis)
             in
             List.iter check (List.rev l); (* use oldest hypothesis in priority *)
	   with Not_found -> ()
	 end
      | _         -> ()
    end;

    (* Check right. *)
    begin match b with
      | FixN(o,f) ->
	 begin
	   try
	     let key = FixN(ODumm,f) in
	     let (before, l, after) = search key ctxt.rfix in
             let check (o', k, used) =
               if less_ordinal o o' && lower_kind a k then
                 (used ();
		  if !debug then Printf.eprintf "Induction applies\n%!";
		  raise Induction_hypothesis)
             in
             List.iter check (List.rev l); (* use oldest hypothesis in priority *)
	   with Not_found -> ()
	 end
      | _         -> ()
    end;

    (* check for loop *)
    let ctxt =
      match (a, b) with
      | (FixM _, _) | (FixN _, _) | (_, FixM _) | (_, FixN _) ->
	 let (a', _) = decompose a in
	 let (b', _) = decompose b in
	 if find_repetition a' b' ctxt.adone then begin
	   if !debug then Printf.eprintf "LOOP\n%!";
	   subtype_error "loop";
	 end;
	 { ctxt with adone = Judgment (a',b') :: ctxt.adone }
      | _ -> ctxt
    in

    (* add induction  *)
    match a, b with
    | FixM(o0,f), FixN(o0',f')  ->
       let o = OLEqu(o0,t,In(binder_from_fun "a" 0 (fun o -> subst f (FixM(o,f))))) in
       if !debug then Printf.eprintf "creating %a <= %a\n%!" print_ordinal o print_ordinal o0;
       let o' = OLEqu(o0',t,NotIn(binder_from_fun "a" 0 (fun o -> subst f' (FixN(o,f'))))) in
       if !debug then Printf.eprintf "creating %a <= %a\n%!" print_ordinal o' print_ordinal o0';
       let key = FixM(ODumm,f) in
       let key' = FixN(ODumm, f') in
       let a0 = FixM(o,f) in
       let b0 = FixN(o',f') in
       let used = trace_subtyping ~ordinal:o t a0 b0 in
       let lfix =
	 let (before, l, after) =
	   try search key ctxt.lfix with Not_found -> ([], [], ctxt.lfix)
	 in
	 List.rev_append before ((key, (o,b0,used)::l) :: after)
       in
       let rfix =
         let (before, l, after) =
	   try search key' ctxt.rfix with Not_found -> ([], [], ctxt.rfix)
	 in
	 List.rev_append before ((key', (o',a0,used)::l) :: after)
       in
       let ctxt = add_left_ind_hyp ctxt a0 a in
       let ctxt = add_right_ind_hyp ctxt b0 b in
       ({ ctxt with lfix; rfix }, a0, b0)

    | FixM(o0,f), _ ->
       let o = OLEqu(o0,t,In(binder_from_fun "a" 0 (fun o -> subst f (FixM(o,f))))) in
       if !debug then Printf.eprintf "creating %a <= %a\n%!" print_ordinal o print_ordinal o0;
       let key = FixM(ODumm,f) in
       let a' = FixM(o,f) in
       let (before, l, after) =
	 try search key ctxt.lfix with Not_found -> ([], [], ctxt.lfix)
       in
       let used = trace_subtyping ~ordinal:o t a' b in
       let lfix = List.rev_append before ((key, (o,b,used)::l) :: after) in
       let ctxt = add_left_ind_hyp ctxt a' a in
       ({ ctxt with lfix }, a', b)

    | _, FixN(o0,f) ->
       let o = OLEqu(o0,t,NotIn(binder_from_fun "a" 0 (fun o -> subst f (FixN(o,f))))) in
       if !debug then Printf.eprintf "creating %a <= %a\n%!" print_ordinal o print_ordinal o0;
       let key = FixN(ODumm, f) in
       let b' = FixN(o,f) in
       let (before, l, after) =
	 try search key ctxt.rfix with Not_found -> ([], [], ctxt.rfix)
       in
       let used = trace_subtyping ~ordinal:o t a b' in
       let rfix = List.rev_append before ((key, (o,a,used)::l) :: after) in
       let ctxt = add_right_ind_hyp ctxt b' b in
       ({ ctxt with rfix }, a, b')

    | _         -> (ctxt, a , b)

let is_mu b f = match subst f (Prod []) with FixM(o,_) -> if b then o = OConv else true | _ -> false
let is_nu b f = match subst f (Prod []) with FixN(o,_) -> if b then o = OConv else true | _ -> false

let subtype : term -> kind -> kind -> unit = fun t a b ->
  let rec subtype ctxt t a b =
    if !debug then Printf.eprintf "%a < %a\n%!" (print_kind false) a (print_kind false) b;
    let _ = trace_subtyping t a b in
    let a = repr a in
    let b = repr b in
    (try
    if a == b || lower_kind a b then () else
    begin match (a,b) with
    (* Handling of unification variables (immitation). *)
    | (UVar ua, UVar ub) ->
       if ua == ub then () else set ua b
    | (UVar ua, _      ) ->
        let k =
          match uvar_occur ua b with
          | Non -> b
	  | Pos -> FixM(OConv,bind_uvar ua b)
          | _   -> bot
        in
        set ua k
    | (_      , UVar ub) ->
        let k =
          match uvar_occur ub a with
          | Non -> a
	  | Pos -> FixM(OConv,bind_uvar ub b)
          | _   -> top
        in
        set ub k

    (* Type definition. *)
    | (TDef(d,a)  , _          ) ->
        subtype ctxt t (msubst d.tdef_value a) b

    | (_          , TDef(d,b)  ) ->
        subtype ctxt t a (msubst d.tdef_value b)

    | (FixM(OConv,f)  , _        ) when is_mu true f ->
       (* Compression of consecutive μs. *)
       let aux x =
         match subst f x with
         | FixM(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       let a' = FixM(OConv, f) in
       let ctxt = add_left_ind_hyp ctxt a' a in
       subtype ctxt t a' b

(*    | (_, FixM(o,f)) when is_mu false f ->
       (* Compression of consecutive μs. *)
       let aux x =
         match subst f x with
         | FixM(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       let b' = FixM(OConv, f) in
       let ctxt = add_right_ind_hyp ctxt b' b in
       subtype ctxt t a b'

    | (FixN(o,f), _) when is_nu false f ->
       (* Compression of consecutive μs. *)
       let aux x =
         match subst f x with
         | FixN(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       let a' = FixN(OConv, f) in
       let ctxt = add_left_ind_hyp ctxt a' a in
      subtype ctxt t a' b*)

    | (_, FixN(OConv,f)) when is_nu true f ->
       (* Compression of consecutive μs. *)
       let aux x =
         match subst f x with
         | FixN(_,g) -> subst g x
         | _       -> assert false (* Unreachable. *)
       in
       let f = binder_from_fun (binder_name f) (binder_rank f) aux in
       let b' = FixN(OConv, f) in
       let ctxt = add_right_ind_hyp ctxt b' b in
       subtype ctxt t a b'

    | _ ->
    let (ctxt, a, b) = check_rec t ctxt a b in
    begin match (a,b) with
    (* Arrow type. *)
    | (Func(a1,b1), Func(a2,b2)) ->
        let f x = appl dummy_position (box t) x in
        let bnd = unbox (bind (lvar_p dummy_position) "x" f) in
        let wit = cnst bnd a2 b2 in
        subtype {ctxt with adone = BArrow true:: ctxt.adone } (dummy_pos (Appl(t,wit))) b1 b2;
        subtype {ctxt with adone = BArrow false:: ctxt.adone } wit a2 a1

    (* Product type. *)
    | (Prod(fsa), Prod(fsb)) ->
        let check_field (l,b) =
          let a = try List.assoc l fsa with Not_found -> subtype_error "Product fields clash." in
	  let ctxt = { ctxt with adone = BProd l::ctxt.adone } in
          subtype ctxt (dummy_pos (Proj(t,l))) a b
        in
        List.iter check_field fsb

    (* Sum type. *)
    | (DSum([]), a)          -> ()
    | (DSum(csa), DSum(csb)) ->
        let check_variant (c,a) =
          let t = unbox
            (case dummy_position (box t) [(c, idt)])
          in
	  let ctxt = { ctxt with adone = BSum c::ctxt.adone } in
	  try
            let b = List.assoc c csb in
            subtype ctxt t a b
	  with
	    Not_found -> subtype ctxt t a (DSum([]))
        in
        List.iter check_variant csa

    (* Universal quantifier. *)
    | (_        , FAll(f)  ) ->
       let b' = subst f (new_ucst t f) in
       let ctxt = add_right_ind_hyp ctxt b' b in
       subtype ctxt t a b'

    | (FAll(f)  , _        ) ->
        let a = subst f (new_uvar ()) in
        subtype ctxt t a b;

    | (UCst(ca)         , UCst(cb)        ) when ca == cb -> ()

    (* Existantial quantifier. *)
    | (Exis(f)  , _        ) ->
       let a' = subst f (new_ecst t f) in
       let ctxt = add_left_ind_hyp ctxt a' a in
       subtype ctxt t a' b

    | (_        , Exis(f)  ) ->
        let b = subst f (new_uvar ()) in
        subtype ctxt t a b;

    | (ECst(ca) , ECst(cb)   ) when ca == cb -> ()

    (* μ and ν - least and greatest fixpoint. *)
    | (_          , FixN(o,f)) ->
       let o = OLess(o, t, NotIn(binder_from_fun "a" 0 (fun o -> FixN(o, f)))) in
       let cst = FixN(o, f) in
       let b' = subst f cst in
       let ctxt = add_right_ind_hyp ctxt b' b in
       subtype ctxt t a b'

    | (FixM(o,f)  , _        ) ->
       let o = OLess(o, t, In(binder_from_fun "a" 0 (fun o -> FixM(o, f)))) in
       let cst = FixM(o, f) in
       let a' = subst f cst in
       let ctxt = add_left_ind_hyp ctxt a' a in
       subtype ctxt t a' b

    | (FixN(OConv,f)  , _        ) ->
       let a' = subst f a in
       let ctxt = add_left_ind_hyp ctxt a' a in
       subtype ctxt t a' b

    | (_          , FixM(OConv,f)) ->
       let b' = subst f b in
       let ctxt = add_right_ind_hyp ctxt b' b in
       subtype ctxt t a b'

    (* Subtype clash. *)
    | (_, _) -> subtype_error "Subtyping clash (no rule apply)."
    end;
    (match a,b with FixM _, _ | _, FixN _ -> trace_pop () | _ -> ())
    end;
    with Induction_hypothesis -> ());
    trace_pop ();

  in
  subtype { adone = [] ; lfix = [] ; rfix = [] } t a b

let generic_subtype : kind -> kind -> unit = fun a b ->
  subtype (generic_cnst a b) a b

let type_check : term -> kind -> unit = fun t c ->
  let c = repr c in
  let rec type_check t c =
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
        begin
          match v.ttype with
          | Some a -> subtype v.value a c
          | None   -> type_check v.value c
        end
    | Prnt(_) ->
       subtype t (Prod []) c
    | FixY(t) ->
       type_check t (Func(c,c))
    | Cnst(cst) ->
        let (_,a,_) = cst in
        subtype t a c
    | TagI(_) ->
       assert false (* Cannot happen. *));
    trace_pop ();
  in
  type_check t c
