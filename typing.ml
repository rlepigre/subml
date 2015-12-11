open Bindlib
open Util
open Ast
open Print

exception Type_error of pos * string
exception Subtype_error of string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype_error : string -> 'a = fun msg ->
  raise (Subtype_error msg)

type subtype_ctxt =
  { lfix : (kind * (ordinal * kind) list) list
  ; rfix : (kind * (ordinal * kind) list) list }

exception Induction_hypothesis

let check_rec : subtype_ctxt -> kind -> kind -> subtype_ctxt * kind * kind =
  fun ctxt a b ->
    let search k l =
      let rec fn acc = function
        | []        -> raise Not_found
        | (x,l)::xs when eq_kind k x -> (acc, l, xs)
        | (x,l)::xs -> fn ((x,l)::acc) xs
      in fn [] l
    in

    (* Check left. *)
    let (ctxt, a, b) =
      match a with
      | FixM(o,f) ->
          begin
            let o = new_olequ o in
            let key = FixM(ODumm,f) in
            let a = FixM(o,f) in
            try
              let (before, l, after) = search key ctxt.lfix in
              let check (o', k) =
                if less_ordinal o o' && lower_kind k b then
                  raise Induction_hypothesis
              in
              List.iter check l;
              let lfix = List.rev_append before ((key, (o,b)::l) :: after) in
              ({ ctxt with lfix }, a, b)
            with Not_found ->
              ({ ctxt with lfix = (key, [(o,b)]) :: ctxt.lfix }, a, b)
          end
      | FixN(_,f) ->
          begin
            let o = ODumm in
            let key = FixN(o,f) in
            try
              let (before, l, after) = search key ctxt.lfix in
              let lfix = List.rev_append before ((key, (o,b)::l) :: after) in
              ({ ctxt with lfix }, a, b)
            with Not_found ->
              ({ ctxt with lfix = (key, [(o,b)]) :: ctxt.lfix }, a, b)
          end
      | _         -> (ctxt, a, b)
    in

    (* Check right. *)
    match b with
    | FixM(o,f) ->
        begin
          let o = ODumm in
          let key = FixM(o,f) in
          try
            let (before, l, after) = search key ctxt.rfix in
            let rfix = List.rev_append before ((key, (o,a)::l) :: after) in
            ({ ctxt with rfix }, a, b)
          with Not_found ->
            ({ ctxt with rfix = (key, [(o,a)]) :: ctxt.rfix }, a, b)
        end
    | FixN(o,f) ->
        begin
          let o = new_olequ o in
          let key = FixN(ODumm, f) in
          let b = FixN(o,f) in
          try
            let (before, l, after) = search key ctxt.rfix in
            let check (o', k) =
              if less_ordinal o o' && lower_kind a k then
                raise Induction_hypothesis
            in
            List.iter check l;
            let rfix = List.rev_append before ((key, (o,a)::l) :: after) in
            ({ ctxt with rfix }, a, b)
          with Not_found ->
            ({ ctxt with rfix = (key, [(o,a)]) :: ctxt.rfix }, a, b)
        end
    | _         -> (ctxt, a , b)

let subtype : bool -> term -> kind -> kind -> unit = fun verbose t a b ->
  let rec subtype ctxt t a b = 
    let a = repr a in
    let b = repr b in
    if verbose then
      Printf.eprintf "Sub: %a ∈ %a ⊆ %a\n%!"
        print_term t (print_kind false) a (print_kind false) b;
    try
    let (ctxt, a, b) = check_rec ctxt a b in
    if a == b then () else
    match (a,b) with
    (* Handling of unification variables (immitation). *)
    | (UVar ua, UVar ub) ->
        if ua == ub then () else
        let c = new_uvar () in
        ua.uvar_val <- Some c;
        ub.uvar_val <- Some c
    | (UVar ua, _      ) ->
        let k =
          match uvar_occur ua b with
          | Non -> b
          | Pos -> subtype_error "Unification variable occuring positively."
          | _   -> bot
        in
        ua.uvar_val <- Some k
    | (_      , UVar ub) ->
        let k =
          match uvar_occur ub a with
          | Non -> a
          | Pos -> subtype_error "Unification variable occuring positively."
          | _   -> top
        in
        ub.uvar_val <- Some k

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
        if not (StrSet.subset lsetb lseta) then
          subtype_error "Product fields clash.";
        let check_field (l,b) =
          let a = List.assoc l fsa in
          subtype ctxt (dummy_pos (Proj(t,l))) a b
        in
        List.iter check_field fsb

    (* Sum type. *)
    | (DSum(csa), DSum(csb)) ->
        let cseta = StrSet.of_list (List.map fst csa) in
        let csetb = StrSet.of_list (List.map fst csb) in
        if not (StrSet.subset cseta csetb) then
          subtype_error "Sum type constructor clash.";
        let check_variant (c,a) =
          let b = List.assoc c csb in
          let t = unbox
            (case dummy_position (box t) [(c, dummy_pos "x", (fun x -> x))])
          in
          subtype ctxt t a b
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
    | (_          , FixM(o,f)) ->
        if lower_kind a b then () else
          let cst = if o = OConv then b else FixM(new_oless o, f) in
          subtype ctxt t a (subst f cst)

    | (FixN(o,f)  , _        ) ->
        if lower_kind a b then () else
          let cst = if o = OConv then a else FixN(new_oless o, f) in
          subtype ctxt t (subst f cst) b

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
              if lower_kind a b then () else
                let cst = FixN(new_oless o, f) in
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
              if lower_kind a b then () else
                let cst = FixM(new_oless o, f) in
              subtype ctxt t (subst f cst) b
        end

    (* Type definition. *)
    | (TDef(d,a)  , _          ) ->
        subtype ctxt t (msubst d.tdef_value a) b

    | (_          , TDef(d,b)  ) ->
        subtype ctxt t a (msubst d.tdef_value b)

    (* Subtype clash. *)
    | (_, _) -> subtype_error "Subtype clash (no rule apply)."

    with Induction_hypothesis -> ()
  in
  subtype { lfix = [] ; rfix = [] } t a b

let generic_subtype : bool -> kind -> kind -> unit = fun vb a b ->
  subtype vb (generic_cnst a b) a b

let type_check : bool -> term -> kind -> unit = fun verbose t c ->
  let subtype = subtype verbose in
  let c = repr c in
  let rec type_check t c =
    if verbose then
      Printf.fprintf stderr "Typ: %a : %a\n%!"
        print_term t (print_kind false) c;
    match t.elt with
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
          type_check (subst f (cnst f cc c)) c
        in
        List.iter check l
    | VDef(v) ->
        begin
          match v.ttype with
          | Some a -> subtype v.value a c
          | None   -> type_check v.value c
        end
    | Prnt(_,t) ->
        type_check t c
    | FixY ->
        subtype t fix_kind c
    | Cnst(cst) ->
        let (_,a,_) = cst in
        subtype t a c
    | TagI(_) ->
        assert false (* Cannot happen. *)
  in
  type_check t c
