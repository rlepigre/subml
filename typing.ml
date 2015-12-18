open Bindlib
open Util
open Ast
open Print
open Trace

exception Type_error of pos * string
exception Subtype_error of string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype_error : string -> 'a = fun msg ->
  raise (Subtype_error msg)

type subtype_ctxt =
  { lfix : (kind * (ordinal * kind * (unit -> unit)) list) list
  ; rfix : (kind * (ordinal * kind * (unit -> unit)) list) list }

exception Induction_hypothesis

let struct_eq k1 k2 =
  match k1, k2 with
  | FixM(_,f1) , FixM(_,f2)
  | FixN(_,f1) , FixN(_,f2) -> eq_kind (subst f1 (TInt (-1))) (subst f2 (TInt (-1)))
  | k1, k2 -> eq_kind k1 k2

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
		   (used (); raise Induction_hypothesis)
	       else if struct_eq k b then
		 subtype_error "loop"
             in
             List.iter check l
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
                 (used (); raise Induction_hypothesis)
	       else if struct_eq a k then
		 subtype_error "loop"
             in
             List.iter check l;
	   with Not_found -> ()
	 end
      | _         -> ()
    end;

    (* add induction left *)
    let (ctxt, a, b) =
      match a with
      | FixM(o,f) ->
         begin
           let o = OLEqu(o,t,In(binder_from_fun "a" 0 (fun o -> subst f (FixM(o,f))))) in
           let key = FixM(ODumm,f) in
           let a = FixM(o,f) in
	   let (before, l, after) =
	     try search key ctxt.lfix with Not_found -> ([], [], ctxt.lfix)
	   in
  	   let ptr = trace_subtyping ~ordinal:o t a b in
           let lfix = List.rev_append before ((key, (o,b,ptr)::l) :: after) in
           ({ ctxt with lfix }, a, b)
         end
      | _         -> (ctxt, a, b)
    in

    (* add induction right. *)
    match b with
    | FixN(o,f) ->
        begin
          let o = OLEqu(o,t,NotIn(binder_from_fun "a" 0 (fun o -> subst f (FixN(o,f))))) in
          let key = FixN(ODumm, f) in
          let b = FixN(o,f) in
          let (before, l, after) =
	    try search key ctxt.rfix with Not_found -> ([], [], ctxt.rfix)
	  in
          let used = trace_subtyping ~ordinal:o t a b in
          let rfix = List.rev_append before ((key, (o,a,used)::l) :: after) in
          ({ ctxt with rfix }, a, b)
        end
    | _         -> (ctxt, a , b)

let subtype : term -> kind -> kind -> unit = fun t a b ->
  let rec subtype ctxt t a b =
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
          | _   -> bot
        in
        set ua k
    | (_      , UVar ub) ->
        let k =
          match uvar_occur ub a with
          | Non -> a
          | _   -> top
        in
        set ub k

    (* Type definition. *)
    | (TDef(d,a)  , _          ) ->
        subtype ctxt t (msubst d.tdef_value a) b

    | (_          , TDef(d,b)  ) ->
        subtype ctxt t a (msubst d.tdef_value b)
    | _ ->
    let (ctxt, a, b) = check_rec t ctxt a b in
    begin match (a,b) with
    (* Arrow type. *)
    | (Func(a1,b1), Func(a2,b2)) ->
        let f x = appl dummy_position (box t) x in
        let bnd = unbox (bind (lvar_p dummy_position) "x" f) in
        let wit = cnst bnd a2 b2 in
        subtype ctxt (dummy_pos (Appl(t,wit))) b1 b2;
        subtype ctxt wit a2 a1

    (* Product type. *)
    | (Prod(fsa), Prod(fsb)) ->
        let lseta = StrSet.of_list (List.map fst fsa) in
        let lsetb = StrSet.of_list (List.map fst fsb) in
        let check_field (l,b) =
          let a = try List.assoc l fsa with Not_found -> subtype_error "Product fields clash." in
          subtype ctxt (dummy_pos (Proj(t,l))) a b
        in
        List.iter check_field fsb

    (* Sum type. *)
    | (DSum([]), a)          -> ()
    | (DSum(csa), DSum(csb)) ->
        let cseta = StrSet.of_list (List.map fst csa) in
        let csetb = StrSet.of_list (List.map fst csb) in
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
        List.iter check_variant csa

    (* Universal quantifier. *)
    | (_        , FAll(f)  ) ->
        let b = subst f (new_ucst t f) in
        subtype ctxt t a b

    | (FAll(f)  , _        ) ->
        let a = subst f (new_uvar ()) in
        subtype ctxt t a b;

    | (UCst(ca)         , UCst(cb)        ) when ca == cb -> ()

    (* Existantial quantifier. *)
    | (Exis(f)  , _        ) ->
        let a = subst f (new_ecst t f) in
        subtype ctxt t a b

    | (_        , Exis(f)  ) ->
        let b = subst f (new_uvar ()) in
        subtype ctxt t a b;

    | (ECst(ca) , ECst(cb)   ) when ca == cb -> ()

    (* μ and ν - least and greatest fixpoint. *)
    | (_          , FixN(o,f)) ->
        begin
          (* Compression of consecutive νs. *)
          match subst f (Prod []) with
          | FixN(_,_) ->
              let aux x =
                match subst f x with
                | FixN(_,g) -> subst g x
                | _       -> assert false (* Unreachable. *)
              in
              let f = binder_from_fun (binder_name f) (binder_rank f) aux in
              subtype ctxt t a (FixN(OConv,f))
          (* Only on consecutive μ. *)
          | _       ->
	     let o = OLess(o, t, NotIn(binder_from_fun "a" 0 (fun o -> FixN(o, f)))) in
             let cst = FixN(o, f) in
             subtype ctxt t a (subst f cst)
        end

    | (FixM(o,f)  , _        ) ->
        begin
          (* Compression of consecutive μs. *)
          match subst f (Prod []) with
          | FixM(_,_) ->
              let aux x =
                match subst f x with
                | FixM(_,g) -> subst g x
                | _       -> assert false (* Unreachable. *)
              in
              let f = binder_from_fun (binder_name f) (binder_rank f) aux in
              subtype ctxt t (FixM(OConv, f)) b
          (* Only on consecutive μ. *)
          | _       ->
	       let o = OLess(o, t, In(binder_from_fun "a" 0 (fun o -> FixM(o, f)))) in
               let cst = FixM(o, f) in
               subtype ctxt t (subst f cst) b
        end

    | (_          , FixM(OConv,f)) -> subtype ctxt t a (subst f b)

    | (FixN(OConv,f)  , _        ) -> subtype ctxt t (subst f a) b


    (* Subtype clash. *)
    | (_, _) -> subtype_error "Subtyping clash (no rule apply)."
    end;
    (match a with FixM _ -> trace_pop () | _ -> ());
    (match b with FixN _ -> trace_pop () | _ -> ())
    end;
    with Induction_hypothesis -> ());
    trace_pop ();

  in
  subtype { lfix = [] ; rfix = [] } t a b

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
