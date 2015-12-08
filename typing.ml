open Bindlib
open Util
open Ast
open Print

exception Type_error of pos * string
exception Subtype_error of string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype_error : string -> unit = fun msg ->
  raise (Subtype_error msg)

type subtype_ctxt =
  { lfix : (kind * (ordinal * kind) list) list
  ; rfix : (kind * (ordinal * kind) list) list }

let subtype : bool -> term -> kind -> kind -> unit = fun verbose t a b ->
  let rec subtype ctxt t a b = 
    let a = repr a in
    let b = repr b in
    if verbose then
      Printf.eprintf "Sub: %a ∈ %a ⊆ %a\n%!"
        print_term t (print_kind false) a (print_kind false) b;
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
          | Pos -> assert false (* TODO Nu *)
          | _   -> bot
        in
        ua.uvar_val <- Some k
    | (_      , UVar ub) ->
        let k =
          match uvar_occur ub a with
          | Non -> a
          | Pos -> assert false (* TODO Mu *)
          | _   -> top
        in
        ub.uvar_val <- Some k

    (* Arrow type. *)
    | (Func(a1,b1), Func(a2,b2)) ->
        let f x = dummy_pos (Appl(t, x)) in
        let wit = cnst (binder_from_fun "x" 1 f) a2 b2 in (* FIXME 1 ? *)
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
          let t = dummy_pos (Reco([])) in (* FIXME FIXME FIXME *)
          subtype ctxt t a b
        in
        List.iter check_variant csa

    (* Universal quantifier. *)
    | (_                , FAll(bo,bbndo,f)) ->
        let b = subst f (new_ucst t bbndo f) in
        subtype ctxt t a b

    | (FAll(ao,abndo,f) , _               ) ->
        let v = match ao with None -> new_uvar () | Some k -> k in
        let a = subst f v in
        subtype ctxt t a b;
        begin
          match abndo with
          | None         -> ()
          | Some (LE, c) -> assert false (* TODO *)
          | Some (GE, c) -> assert false (* TODO *)
        end

    | (UCst(ca)         , UCst(cb)        ) when ca == cb -> ()

    (* Existantial quantifier. *)
    | (Exis(ao,abndo,f) , _               ) ->
        let a = subst f (new_ecst t abndo f) in
        subtype ctxt t a b

    | (_                , Exis(bo,bbndo,f)) ->
        let v = match bo with None -> new_uvar () | Some k -> k in
        let b = subst f v in
        subtype ctxt t a b;
        begin
          match bbndo with
          | None         -> ()
          | Some (LE, c) -> assert false (* TODO *)
          | Some (GE, c) -> assert false (* TODO *)
        end

    | (ECst(ca)   , ECst(cb)   ) when ca == cb -> ()

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
          | FixN(o',_) ->
              let aux x =
                match subst f x with
                | FixN(_,g) -> subst g x
                | _       -> assert false (* Unreachable. *)
              in
              let o = prod_ordinal o o' in
              let f = binder_from_fun (binder_name f) (binder_rank f) aux in
              subtype ctxt t a (FixN(o,f))
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
          | FixM(o',_) ->
              let aux x =
                match subst f x with
                | FixM(_,g) -> subst g x
                | _       -> assert false (* Unreachable. *)
              in
              let o = prod_ordinal o o' in
              let f = binder_from_fun (binder_name f) (binder_rank f) aux in
              subtype ctxt t (FixM(o, f)) b
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
  in
  subtype { lfix = [] ; rfix = [] } t a b

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

let type_infer : bool -> term -> kind option -> kind = fun verbose t ko ->
  match ko with
  | None   -> let a = new_uvar () in
              type_check verbose t a;
              generalize (repr a)
  | Some k -> type_check verbose t k; k
