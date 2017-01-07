(****************************************************************************)
(**{3                   Typing and subtyping algorithms                    }*)
(****************************************************************************)
open Bindlib
open Ast
open Binding
open Print
open Position
open Compare
open Term
open Generalise
open TypingBase
open Error
open LibTools

exception Induction_hyp of Sct.index

type induction =
  | UseInduction of Sct.index
  | NewInduction of (schema * kind * kind * (ordi * ordi) list) option

(* check is a subtyping can be deduced from an induction hypothesis,
   if this is not possible, the subtyping may be added as induction
   hypothesis that we can use later *)
let check_rec
    : term -> subtype_ctxt -> kind -> kind -> induction * subtype_ctxt
  = fun t ctxt a b ->
    begin match full_repr a, full_repr b with
    | KFixM(o,_), KFixM(o',_)
    | KFixN(o',_), KFixN(o,_) ->
       (* HEURISTIC THAT AVOID LOOPS, by comparing ordinals
          it forces some unification of ordinal variables.
          If we keep ordinal variables, it may loops on
          useful examples.
          IMPROVE: can we do better ?*)
       ignore (eq_ordi ctxt.positive_ordis o o')
    | _ -> ()
    end;

    (* the test (has_uvar a || has_uvar b) is important to
       - avoid occur chek for induction variable
       - to preserve, when possible, the invariant that no ordinal <> OConv occur in
       positive mus and negative nus *)
    try
      if (match a with KFixM _ -> false | KFixN _ -> has_leading_exists a | _ -> true) &&
         (match b with KFixN _ -> false | KFixM _ -> has_leading_forall b | _ -> true)
      then raise Exit;
      (match full_repr a with KMRec _ | KNRec _ -> raise Exit | _ -> ());
      (match full_repr b with KMRec _ | KNRec _ -> raise Exit | _ -> ());
      (* Search for the inductive hypothesis *)
      Io.log_sub "IND %a < %a (%a)\n%!" (print_kind false) a (print_kind false) b
        print_positives ctxt;
      let pos = ctxt.positive_ordis in
      let (schema, os, (os0,tpos,k1,k2)) = generalise pos (SchKind a) b ctxt.call_graphs in
      let k1 = match k1 with
        | SchTerm _ -> assert false
        | SchKind k -> k
      in
      let fnum = schema.sch_index in
      add_call ctxt fnum os false;
      let ctxt = { ctxt with
        sub_induction_hyp = schema::ctxt.sub_induction_hyp;
        positive_ordis = tpos;
        top_induction = (fnum, os0)
      } in
      let calls = List.fold_left (fun acc schema' ->
        (* hypothesis apply if same type up to the parameter and same positive ordinals.
           An inclusion beween p' and p0 should be enough, but this seems complete that
           way *)
        let (ov,pos',a',b') = recompose_kind schema' in
        Io.log_sub "TESTING %a = %a\n%a = %a\n\n%!"
          (print_kind false) k1  (print_kind false) a'
          (print_kind false) k2  (print_kind false) b';
        if eq_kind tpos k1 a' && eq_kind tpos b' k2 &&
          List.for_all (fun o1 ->
            match orepr o1 with OConv | OSucc _ -> true | _ ->
               List.exists (eq_ordi tpos o1) tpos) pos'
        then (
          Io.log_sub "By induction\n\n%!";
          build_call ctxt schema'.sch_index ov true :: acc)
        else acc) [] (List.tl ctxt.sub_induction_hyp) in
      let calls = List.map (fun (_,_,m1,_ as call) -> (score_mat m1, call)) calls in
      let calls = List.sort (fun (s1,_) (s2,_) -> compare s2 s1) calls in
      (match calls with
      | (_,(index,_,_,_ as call))::_ ->
         Sct.new_call ctxt.call_graphs call;
        raise (Induction_hyp index)
      | [] -> ());
      Io.log_sub "NEW %a < %a\n%!" (print_kind false) k1 (print_kind false) k2;
      let tros = List.map2 (fun (_,o1) (_,o2) ->
        let o2 = match o2 with OVari _ -> OConv | _ -> o2 in
        (o1,o2)) os0 os in
      (NewInduction (Some (schema, k1, k2, tros)), ctxt)
    with Exit | FailGeneralise -> (NewInduction None, ctxt)
       | Induction_hyp n -> (UseInduction n, ctxt)

let fixpoint_depth = ref 1

(** Used when we can not apply any induction hyp, to give a descent error message *)
exception NoProof of typ_rule

let rec subtype : subtype_ctxt -> term -> kind -> kind -> sub_prf = fun ctxt0 t0 a0 b0 ->
  Io.log_sub "%a\n  ∈ %a\n  ⊂ %a\n  %a\n\n%!"
    (print_term false) t0 (print_kind false) a0 (print_kind false) b0
    print_positives ctxt0;
  let a = full_repr a0 in
  let b = full_repr b0 in
  if eq_kind ctxt0.positive_ordis a b then
    (ctxt0.positive_ordis, t0, a0, b0, Sub_Lower)
  else try try
    let rule = match (a,b) with
    | (KMRec(ptr,a), _           ) ->
       Sub_And_l(subtype ctxt0 t0 a b0)

    | (_           , KNRec(ptr,b))->
       Sub_Or_r(subtype ctxt0 t0 a0 b)

    | (KNRec(ptr,a), KUVar _     )
        when Subset.test (eq_ordi ctxt0.positive_ordis) ptr ctxt0.positive_ordis ->
       Sub_Or_l(subtype ctxt0 t0 a b0)

    | (KUVar _     , KMRec(ptr,b))
        when Subset.test (eq_ordi ctxt0.positive_ordis) ptr ctxt0.positive_ordis ->
       Sub_And_r(subtype ctxt0 t0 a0 b)

    (* unification. (sum and product special) *)
    | (KUVar(ua,os), KProd(l))
       when (match uvar_state ua with DSum _ -> false | _ -> true) ->
       let l0 = match uvar_state ua with
         | Free   -> []
         | Prod l -> l
         | DSum _ -> assert false
       in
       let l1 = ref l0 in
       let res = ref [] in
       List.iter (fun (s,k) ->
         let t' = dummy_pos (TProj(t0,s)) in
         try
           let prf = subtype ctxt0 t' (msubst (List.assoc s l0) os) k  in
           res := (s,prf) :: !res
         with
           Not_found ->
             let f = bind_ordis os k in
             l1 := (s,f)::!l1;
             let prf = subtype ctxt0 t' (msubst f os) k  in
             res := (s,prf) :: !res) l;
       Timed.(ua.uvar_state := Unset (Prod !l1));
       Sub_Prod(!res)

    | (KDSum(l)   , KUVar(ub,os))
       when (match uvar_state ub with Prod _ -> false | _ -> true) ->
       let l0 = match uvar_state ub with
         | Free   -> []
         | DSum l -> l
         | Prod _ -> assert false
       in
       let l1 = ref l0 in
       let res = ref [] in
       List.iter (fun (s,k) ->
         let t' = unbox (tcase dummy_position (box t0) [(s, idt)] None) in
         try
           let prf = subtype ctxt0 t' k (msubst (List.assoc s l0) os)  in
           res := (s,prf) :: !res
         with
           Not_found ->
             let f = bind_ordis os k in
             l1 := (s,f)::!l1;
             let prf = subtype ctxt0 t' k (msubst f os) in
             res := (s,prf) :: !res) l;
       Timed.(ub.uvar_state := Unset (DSum !l1));
       Sub_DSum(!res)

    (* Handling of unification variables, same variable different
       parameters: keep the common one only. *)
    | (KUVar(ua,osa),KUVar(ub,osb)) when eq_uvar ua ub ->
       let osal = Array.to_list osa in
       let osbl = Array.to_list osb in
       let (_,os) = List.fold_left2 (fun (i,acc) o1 o2 ->
         if strict_eq_ordi o1 o2 then
           (i+1,i::acc)
         else
           (i+1,acc)) (0,[]) osal osbl
       in
       let os = Array.of_list os in
       let new_len = Array.length os in
       if new_len <> ua.uvar_arity then (
         let u = new_kuvara new_len in
         let f = unbox (mbind mk_free_ovari (Array.make ua.uvar_arity "α") (fun x ->
           box_apply (fun os -> KUVar(u,os)) (box_array (Array.init new_len (fun i ->
             x.(os.(i)))))))
         in
         (* this will use the uvar_state if it is not Free, we could try
            to delay this *)
         safe_set_kuvar sNeg ua f osa);
       let (_,_,_,_,r) = subtype ctxt0 t0 a0 b0 in r

    (* Handling of unification variables (immitation). *)
    | ((KUVar(ua,osa) as a),(KUVar(ub,osb) as b)) ->
       begin (* make the correct choice, depending if DSum or Prod *)
          match (uvar_state ua, uvar_state ub) with
          | _, DSum _ -> safe_set_kuvar sNeg ua (bind_ordis osa b) osa
          | Prod _, _ -> safe_set_kuvar sPos ub (bind_ordis osb a) osb
          | _ ->
               let osal = Array.to_list osa in
               let osbl = Array.to_list osb in
               let os = List.fold_left (fun acc o ->
                 if List.exists (strict_eq_ordi o) acc then acc
                 else
                   if   (List.exists (strict_eq_ordi o) osal &&
                         List.exists (strict_eq_ordi o) osbl)
                     || (List.exists (strict_eq_ordi o) osal
                         && not (kuvar_ord_occur ub o))
                     || (List.exists (strict_eq_ordi o) osbl
                         && not (kuvar_ord_occur ua o))
                   then o::acc
                   else acc) [] (osal @ osbl)
               in
               let os = Array.of_list os in
               let new_len = Array.length os in
               let state =
                 match (uvar_state ua, uvar_state ub) with
                 | Free, Free -> Free
                 | DSum l, _ ->
                    DSum (List.map (fun (s,f) ->
                      (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                        bind_fn os x (msubst f osa))))) l)
                 | _, Prod l ->
                    Prod (List.map (fun (s,f) ->
                      (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                        bind_fn os x (msubst f osb))))) l)
                 | _ -> assert false
               in
               let u = new_kuvara ~state new_len in
               let k = KUVar(u,os) in
               (* NOTE: the call to  bind_fn above may (very rarely) instanciate
                  ua or ub, so we added a test to avoid an assert false  *)
               if is_unset ua then (
                 Timed.(ua.uvar_state := Unset Free);
                 safe_set_kuvar sNeg ua (bind_ordis osa k) osa);
               if is_unset ub then (
                 Timed.(ub.uvar_state := Unset Free);
                 safe_set_kuvar sPos ub (bind_ordis osb k) osb);
        end;
        let (_,_,_,_,r) = subtype ctxt0 t0 a0 b0 in r

    | (KUVar(ua,os), b            ) ->
        safe_set_kuvar sNeg ua (bind_ordis os b0) os;
        let (_,_,_,_,r) = subtype ctxt0 t0 a0 b0 in r

    | (a           ,(KUVar(ub,os)))  ->
        safe_set_kuvar sPos ub (bind_ordis os a0) os;
        let (_,_,_,_,r) = subtype ctxt0 t0 a0 b0 in r

    (* quantification rule introducing witness before induction *)
    | (_           , KKAll(f)    ) ->
        let p = subtype ctxt0 t0 a0 (subst f (KUCst(t0,f,true))) in
        Sub_KAll_r(p)

    | (KKExi(f)    , _           ) ->
        let p = subtype ctxt0 t0 (subst f (KECst(t0,f,true))) b0 in
        Sub_KExi_l(p)

    | (_           , KOAll(f)    ) ->
        let p = subtype ctxt0 t0 a0 (subst f (OLess(OConv, NotIn(t0,f)))) in
        Sub_OAll_r(p)

    | (KOExi(f)    , _           ) ->
        let p = subtype ctxt0 t0 (subst f (OLess(OConv, In(t0,f)))) b0 in
        Sub_OExi_l(p)


    | _ -> raise Exit
  in (ctxt0.positive_ordis, t0, a0, b0, rule)
  with Exit ->
  let (ind_res, ctxt) = check_rec t0 ctxt0 a b in
  match ind_res with
  | UseInduction n -> (ctxt.positive_ordis, t0, a0, b0, Sub_Ind n)
  | NewInduction ind_ref ->
  let (finalise_proof,t,a,b,a0,b0) = match ind_ref with
    | None -> ((fun x -> x),t0,a,b,a0,b0)
    | Some(n,a,b,tros) ->
       let a = full_repr a and b = full_repr b in
       let t1 = unbox (generic_tcnst (box a) (box b)) in
       ((fun x -> ctxt0.positive_ordis,t0,a0,b0,Sub_Gen(n, tros, x)),
        t1, a, b, a, b)
  in
  let rule =
    match (a,b) with
    (* Arrow type. *)
    | (KFunc(a1,b1), KFunc(a2,b2)) ->
       let wit =
         let f x = tappl dummy_position (box t) (box_apply dummy_pos x) in
         let bnd = unbox (bind mk_free_tvari "x" f) in
         unbox (tcnst bnd (box a2) (box b2))
       in
        (* NOTE: the heuristic below works well for Church like encoding *)
       if has_uvar b1 then
         let wit = if strict_eq_kind a2 (KProd []) then dummy_pos (TReco []) else wit in
         let p2 = subtype ctxt (dummy_pos (TAppl(t, wit))) b1 b2 in
         let p1 = subtype ctxt wit a2 a1 in
         Sub_Func(p1, p2)
       else
         let p1 = subtype ctxt wit a2 a1 in
         let wit = if strict_eq_kind a2 (KProd []) then dummy_pos (TReco []) else wit in
         let p2 = subtype ctxt (dummy_pos (TAppl(t, wit))) b1 b2 in
         Sub_Func(p1, p2)

    (* Product type. *)
    | (KProd(fsa)  , KProd(fsb)  ) ->
        let check_field (l,b) =
          let a =
            try List.assoc l fsa
            with Not_found -> subtype_error ("Product fields clash: " ^ l)
          in
          (l, subtype ctxt (dummy_pos (TProj(t,l))) a b)
        in
        let ps = List.map check_field fsb in
        Sub_Prod(ps)

    (* Sum type. *)
    | (KDSum(csa)  , KDSum(csb)  ) ->
        let check_variant (c,a) =
          let t = unbox (tcase dummy_position (box t) [(c, idt)] None) in
          let b =
            try List.assoc c csb
            with Not_found -> subtype_error ("Constructor clash: " ^ c)
          in
          (c, subtype ctxt t a b)
        in
        let ps = List.map check_variant csa in
        Sub_DSum(ps)

    (* μl and νr rules. *)
    | (_           , KFixN(o,f)  ) ->
        let o', ctxt =
          match orepr o with
          | OSucc o' -> o', ctxt
          | o ->
             let g = bind mk_free_ovari (binder_name f) (fun o ->
               bind_apply (Bindlib.box f) (box_apply (fun o -> KFixN(o,f)) o))
             in
             let o' = opred o (Some (NotIn(t,unbox g))) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi false) o' (print_ordi false) o;
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi true) o' (print_ordi true) o;
        let cst = KFixN(o', f) in
        let prf = subtype ctxt t a0 (subst f cst) in
        Sub_FixN_r prf

    | (KFixM(o,f)   , _          ) ->
        let o', ctxt =
          match orepr o with
          | OSucc o' -> o', ctxt
          | o ->
             let g = bind mk_free_ovari (binder_name f) (fun o ->
               bind_apply (Bindlib.box f) (box_apply (fun o -> KFixM(o,f)) o))
             in
             let o' = opred o (Some (In(t,unbox g))) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi false) o' (print_ordi false) o;
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi true) o' (print_ordi true) o;
        let cst = KFixM(o', f) in
        let prf = subtype ctxt t (subst f cst) b0 in
        Sub_FixM_l prf

    (* μr and νl rules. *)
    | (KFixN(o,f)  , _           ) ->
       (* TODO; better to have multi valued ordinals than backtracking *)
       let rec fn = function
         | [] -> subtype_error "Subtyping clash (no rule apply for left nu)."
         | o'::l ->
            let save = Timed.Time.save () in
            try
              (match orepr o with OUVar(p,os) -> set_ouvar p (obind_ordis os o') | _ -> ());
              let o'' = opred o' None in
              let a = if o' = OConv then a else KFixN(o'',f) in
              let p = subtype ctxt t (subst f a) b0 in
              if not (is_positive ctxt.positive_ordis o') then raise Not_found;
              check_sub_proof p;
              Sub_FixN_l(p)
            with Not_found | Error _ -> Timed.Time.rollback save; fn l
       in
       fn (possible_positive ctxt o)

    | (_           , KFixM(o,f)  ) ->
       (* TODO; better to have multi valued ordinals than backtracking *)
       let rec fn = function
         | [] -> subtype_error "Subtyping clash (no rule apply for right mu)."
         | o'::l ->
            let save = Timed.Time.save () in
            try
              (match orepr o with OUVar(p,os) -> set_ouvar p (obind_ordis os o') | _ -> ());
              let o'' = opred o' None in
              let b = if o' = OConv then b else KFixM(o'',f) in
              let p = subtype ctxt t a0 (subst f b) in
              if not (is_positive ctxt.positive_ordis o') then raise Not_found;
              check_sub_proof p;
              Sub_FixM_r(p)
            with Not_found | Error _ -> Timed.Time.rollback save; fn l
       in
       fn (possible_positive ctxt o)

    (* quantification rule introducing unification variable last *)
    | (KKAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (new_kuvar ())) b0 in
        Sub_KAll_l(p)

    | (_           , KKExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (new_kuvar ())) in
        Sub_KExi_r(p)

    | (KOAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (new_ouvar ())) b0 in
        Sub_OAll_l(p)

    | (_           , KOExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (new_ouvar ())) in
        Sub_OExi_r(p)

    | (KNRec(ptr, a), _          )
        when Subset.test (eq_ordi ctxt.positive_ordis) ptr ctxt.positive_ordis ->
       Sub_And_l(subtype ctxt t a b0)

    | (_           , KMRec(ptr, b))
        when Subset.test (eq_ordi ctxt.positive_ordis) ptr ctxt.positive_ordis ->
       Sub_Or_r(subtype ctxt t a0 b)

    (* Subtype clash. *)
    | (_           , _           ) ->
       subtype_error "Subtyping clash (no rule apply)."
  in finalise_proof (ctxt.positive_ordis, t, a0, b0, rule)
  with Subtype_error e -> (ctxt0.positive_ordis, t0, a0, b0, Sub_Error e)
         | Occur_check -> (ctxt0.positive_ordis, t0, a0, b0, Sub_Error "Occur_check")

(** A boolean test for subtyping *)
and is_subtype ctxt t a b =
  Timed.pure_test (fun () ->
    (** protect the call graph *)
    let ctxt = { ctxt with call_graphs = Sct.copy ctxt.call_graphs} in
    let prf = subtype ctxt t a b in
    try check_sub_proof prf; true with Error _ -> false) ()

and type_check : subtype_ctxt -> term -> kind -> typ_prf = fun ctxt t c ->
  let c = repr c in
  Io.log_typ "%a :\n  %a\n  %a\n\n%!"
    (print_term false) t (print_kind false) c print_positives ctxt;
  let r =
    try
      match t.elt with
      | TCoer(t,a) ->
         let p1 = subtype ctxt t a c in
         let p2 = type_check ctxt t a in
         Typ_Coer(p1, p2)
      | TMLet(b,x,bt) ->
         let k = match x with
           | None -> c
           | Some t -> (match t.elt with
                       | TCnst(_,c,_) -> c
                       | TDefi d -> d.ttype
                       | _ -> assert false (* NOTE: Only variable allowed by parsing *))
         in
         let oargs = Array.init (mbinder_arity b) (fun n -> new_ouvar ()) in
         let b = msubst b oargs in
         let kargs = Array.init (mbinder_arity b) (fun n -> new_kuvar ()) in
         let k' = msubst b kargs in
         let t = mmsubst bt oargs kargs in
         let x = from_opt x t in
         if is_subtype ctxt x k k' then
           let p = type_check ctxt t c in
           Typ_Nope(p)
         else
           type_error "Type matching failed"

      | TAbst(ao,f) ->
         let a = match ao with None -> new_kuvar () | Some a -> a in
         let b = new_kuvar () in
         let ptr = Subset.create ctxt.positive_ordis in
         let c' = KNRec(ptr,KFunc(a,b)) in
         let p1 = subtype ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let wit = unbox (tcnst f (box a) (box b)) in
         let p2 = type_check ctxt (subst f wit.elt) b in
         Typ_Func_i(p1, p2)
      | TAppl(t,u) when is_neutral t && not (is_neutral u)->
         let a =
           if strict_eq_term u (dummy_pos (TReco []))
           then KProd [] else new_kuvar () in
         let ptr = Subset.create ctxt.positive_ordis
         in
         let p2 = type_check ctxt t (KMRec(ptr,KFunc(a,c))) in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let p1 = type_check ctxt u a in
         Typ_Func_e(p1, p2)
      | TAppl(t,u) ->
         let a = if strict_eq_term u (dummy_pos (TReco []))
           then KProd [] else new_kuvar ()
         in
         let p1 = type_check ctxt u a in
         let p2 = type_check ctxt t (KFunc(a,c)) in
         Typ_Func_e(p1, p2)
      | TReco(fs) ->
         let ts = List.map (fun (l,_) -> (l, new_kuvar ())) fs in
         let c' = KProd(ts) in
         let ptr = Subset.create ctxt.positive_ordis in
         let c' =  if is_normal t then KNRec(ptr,c') else c' in
         let p1 = subtype ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let check (l,t) =
           let cl = List.assoc l ts in type_check ctxt t cl
         in
         let p2s = List.map check fs in
         Typ_Prod_i(p1, p2s)
      | TProj(t,l) ->
         let c' = new_kuvar ~state:(Prod [(l,constant_mbind 0 c)]) () in
         let p = type_check ctxt t c' in
         Typ_Prod_e(p)
      | TCons(d,v) ->
         let a = new_kuvar () in
         let c' = new_kuvar ~state:(DSum [(d,constant_mbind 0 a)]) () in
         let ptr = Subset.create ctxt.positive_ordis in
         let c' = if is_normal t then KNRec(ptr,c') else c' in
         let p1 = subtype ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let p2 = type_check ctxt v a in
         Typ_DSum_i(p1, p2)
      | TCase(t,l,d) ->
         let ts = List.map (fun (c,_) -> (c, new_kuvar ())) l in
         let k =
           match d with
             None ->
               KDSum ts
           | _    ->
              let ts = List.map (fun (c,_) -> (c, constant_mbind 0 (List.assoc c ts))) l in
              new_kuvar ~state:(DSum ts) ()
         in
         let ptr = Subset.create ctxt.positive_ordis in
         let p1 = type_check ctxt t (KMRec(ptr,k)) in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let check (d,f) =
           let cc = List.assoc d ts in
           type_check ctxt f (KFunc(cc,c))
         in
         let p2s = List.map check l in
         let p3 =
           match d, k with
           | None, _ -> None
           | Some f, KUVar({ uvar_state = { contents = Unset (DSum ts) }}, os)  ->
              let ts = List.filter (fun (c,_) -> not (List.mem_assoc c l)) ts in
              let ts = List.map (fun (c,k) -> (c, msubst k os)) ts in
              Some (type_check ctxt f (KFunc(KDSum ts,c)))
           | _ -> assert false
         in
         Typ_DSum_e(p1, p2s, p3)
      | TDefi(v) ->
         let p = subtype ctxt v.value v.ttype c in
         Typ_Defi(p)
      | TPrnt(_) ->
         let p = subtype ctxt t (KProd []) c in
         Typ_Prnt(p)
      | TFixY(do_subsume,depth,f) ->
         check_fix ctxt t do_subsume depth f c
      | TCnst(_,a,b) ->
         let p = subtype ctxt t a c in
         Typ_Cnst(p)
      | TVari _ | TVars _ -> assert false
    with
    | Subtype_error msg (* FIXME: could we avoid Subtype_error in typing.
                           It not, should use the same exception *)
    | Type_error msg -> Typ_Error msg
    | Occur_check    -> Typ_Error "occur_check"
    | Sys.Break      -> interrupted t.pos
  in (ctxt.positive_ordis, t, c, r)

and subsumption acc = function
  | [] -> List.rev acc
  | (ctxt,_,t,c,ptr,subsumed as head)::tail ->
     let forward = ref false in
     let rec gn acc' = function
       | [] -> subsumption (head::List.rev acc') tail
       | (ctxt',_,t',c',ptr',subsumed' as head')::tail' ->
          let prf = subtype ctxt t c' c in
          if try check_sub_proof prf; true with Error _ -> false then begin
            assert (not !forward);
            subsumed' := ctxt :: !subsumed @ !subsumed';
            ptr := Indirect (prf,ptr');
            subsumption acc tail
          end else
          let prf = subtype  ctxt t' c c' in
          if try check_sub_proof prf; true with Error _ -> false then begin
            forward := true;
            subsumed := ctxt' :: !subsumed' @ !subsumed;
            ptr' := Indirect (prf,ptr);
            gn acc' tail'
          end else
            gn (head'::acc') tail'
     in gn [] acc

and breadth_first proof_ptr hyps_ptr f remains do_subsume depth =
      if depth = 0 && !remains <> [] then
         (* the fixpoint was unrolled as much as allowed, and
            no applicable induction hyp was found. *)
        Typ_YGen(proof_ptr)
      else
        (* otherwise we unroll once more, and type-check *)
        let l = List.map (fun (ctxt,c,ptr) ->
          let e = TFixY(do_subsume,depth-1,f) in
          let t0 = dummy_pos e in
          let t =  subst f e in
          ctxt,t0,t,c,ptr,ref []) !remains
        in
        let l = if do_subsume then subsumption [] l else l in
        let l = List.map (fun (ctxt,t0,t,c,ptr,subsumed) ->
          let (schema, os,(os0, tpos, _, c0)) =
            try generalise ctxt.positive_ordis (SchTerm t0) c ctxt.call_graphs
            with FailGeneralise -> assert false
          in
          let tros = List.combine (List.map snd os) (List.map snd os0) in
          let fnum = schema.sch_index in
          Io.log_typ "Adding induction hyp (1) %a:\n  %a => %a\n%!"
            Sct.prInd fnum (print_kind false) c (print_kind false) c0;
          List.iter (fun ctxt -> add_call ctxt fnum os false) (ctxt::!subsumed);
          if os <> [] then hyps_ptr := schema :: !hyps_ptr;
          let ctxt = { ctxt with top_induction = (fnum, os0);
                                 positive_ordis = tpos} in
          Some (ctxt,t0,t,c0,schema,tros,ptr)) l
        in
        let l = List.fold_left (fun acc -> function
          | None -> acc
          | Some x -> x::acc) [] l
        in
        remains := [];

        List.iter (fun (ctxt,t0,t,c,schema,tros,ptr) ->
          let prf = type_check ctxt t c in
          let prf = (ctxt.positive_ordis, t0, c, Typ_Yufl prf) in
          ptr := Direct (schema,tros, prf)) l;
        if !remains = [] then
          Typ_YGen(proof_ptr)
        else
          breadth_first proof_ptr hyps_ptr f remains do_subsume (depth-1)

and search_induction depth ctxt t a c0 hyps =
  (* fn search for an applicable inductive hypothesis *)
  Io.log_typ "searching induction hyp (1):\n  %a %a\n%!"
    (print_kind false) c0 print_positives ctxt;
  (* NOTE: HEURISTIC THAT AVOID SOME FAILURE, BY FORCING SOME UNIFICATIONS,
     can we do better ? *)
  let _ = is_subtype ctxt t a c0 in
  let errProof = ref (Typ_Error "Can not find induction hyp") in

  let rec fn acc = function
    | [] -> acc
    | schema :: hyps ->
       try
         let (ov, pos, _, a) = recompose schema in
         Io.log_typ "searching induction hyp (2) with %a %a ~ %a <- %a:\n%!"
           Sct.prInd schema.sch_index (print_kind false) a (print_kind false) c0
           print_positives { ctxt with positive_ordis = pos};
           (* need full subtype to rollback unification of variables if it fails *)
         let time = Timed.Time.save () in
         let prf = subtype ctxt t a c0 in
         (try
           check_sub_proof prf;
           Io.log_sub "eq ok\n%!";
           if not (List.for_all (fun o1 ->
             match orepr o1 with OConv | OSucc _ -> true | _ ->
             List.exists (eq_ordi ctxt.positive_ordis o1)
               ctxt.positive_ordis) pos)
           then raise Exit;
           Io.log_typ "induction hyp applies with %a %a ~ %a <- %a:\n%!"
             Sct.prInd schema.sch_index (print_kind false) a (print_kind false) c0
             print_positives { ctxt with positive_ordis = pos}
         with (Exit | Error _) as e ->
            if e <> Exit then errProof := Typ_YInd(schema.sch_index,prf);
           Timed.Time.rollback time;
           raise Exit);
         fn ((prf, build_call ctxt schema.sch_index ov true) :: acc) hyps
       with Exit -> fn acc hyps
  in
  (* HEURISTIC: try induction hypothesis with more parameters first.
     useful for flatten2 in lib/list.typ *)
  let hyps = List.sort (fun {sch_judge = both} {sch_judge = both'} ->
    mbinder_arity both' - mbinder_arity both) hyps in
  if depth > 0 then
       (* If the depth is not zero, only apply the above heuristic, but
          do not search really the induction hypothesis *)
    raise (NoProof !errProof)
  else (
    let calls = fn [] hyps in
    let calls = List.map (fun (prf,(index,_,m1,_ as call)) ->
      let (a,b,c as s) = score_mat m1 in
      Io.log_mat "score: (%d,%d,%d)\n%!" a b c;
      (s, prf, call)) calls in
    Io.log_mat "\n%!";
    let calls = List.sort (fun (s1,_,_) (s2,_,_) -> compare s2 s1) calls in
    match calls with
    | (_,prf,(index,_,_,_ as call))::_ ->
       Sct.new_call ctxt.call_graphs call;
      Typ_YInd(index,prf)
    | [] -> Io.log_typ "no induction hyp found\n%!"; raise (NoProof !errProof))

(* Check if the typing of a fixpoint comes from an induction hypothesis *)
and check_fix ctxt t do_subsume depth f c0 =
  (* filter the relevant hypothesis *)
  let hyps = List.filter (function (f',_,_,_) -> f' == f) ctxt.fix_induction_hyp in
  let a, remains, hyps =
    match hyps with
    | [(_,a,l,r)] -> a, r, Some (l) (* see comment on Rec above *)
    | [] -> c0, ref [], None
    | _ -> assert false
  in
  (* This is the subtyping that means that the program is typed, as in ML
     x : A |- t : A => Y \x.t : A
     This helps for polymorphic program ... But is wrong if initial type
     has ordinal parameters
  *)
  match hyps with
  | None ->
    (* No induction hypothesis was found, we create a new one, unroll
       the fixpoint and initiate the proof search in breadth-first.
       Remark: in general, fixpoint are unrolled twice (except when
       using explicitely sized types).  The first time, mu/nu are
       annotated with size, the second time we try applying the
       induction hypothesis.
       Fixpoint may be unrolled more that twice. This is important for some
       function. However, this is expensive, if subsumption fails ...
    *)
    let hyps_ptr = ref [] in
    let ctxt =
      { ctxt with
        fix_induction_hyp = (f,a,hyps_ptr, remains)::ctxt.fix_induction_hyp;
      }
    in
    let proof_ptr = ref Todo in
    assert (!remains = []);
    remains := (ctxt, c0, proof_ptr) :: !remains;
    (* The main function doing the breadth-first search for the proof *)
    (* n : the current depth *)
    let depth = if has_leading_ord_quantifier c0 then depth + 1 else depth in
    breadth_first proof_ptr hyps_ptr f remains do_subsume depth

  (* we reach this point when we are call from type_check inside
     breadth_fitst above *)
  | Some ({contents = hyps }) ->
    try search_induction depth ctxt t a c0 hyps with NoProof rule ->
      (* No inductive hypothesis applies, we add a new induction hyp and
         record the unproved judgment with the other *)
      let ptr = ref Todo in
      Io.log_typ "adding remain at %d %a\n%!" depth (print_kind false) c0;
      remains := (ctxt, c0, ptr) :: !remains;
      Typ_YGen(ptr)

let subtype : ?ctxt:subtype_ctxt -> ?term:term -> kind -> kind -> sub_prf * Sct.call_table
  = fun ?ctxt ?term a b ->
    let term = unbox (generic_tcnst (box a) (box b)) in
    let ctxt =
      {  (empty_ctxt ()) with
          call_graphs = Sct.init_table ()
        ; top_induction = (Sct.root, [])
      }
    in
    let p = subtype ctxt term a b in
    let call_graphs = Sct.inline ctxt.call_graphs in
    if not (Sct.sct call_graphs) then loop_error dummy_position;
    check_sub_proof p;
    (p, call_graphs)

let type_check : term -> kind option -> kind * typ_prf * Sct.call_table =
  fun t k ->
    let k = from_opt' k new_kuvar in
    let ctxt = empty_ctxt () in
    let (prf, calls) =
      try
        let p = type_check ctxt t k in
        check_typ_proof p;
    let call_graphs = Sct.inline ctxt.call_graphs in
        if not (Sct.sct call_graphs) then loop_error t.pos;
        reset_all ();
        (p, call_graphs)
      with e -> reset_all (); raise e
    in
    let fn (v, os) =
      match !(v.uvar_state) with
      | Set _ -> false
      | Unset Free   -> true
      | Unset (DSum  l) ->
         let k = mbind_assoc kdsum v.uvar_arity l in
         safe_set_kuvar All v k os; false (* FIXME: should not trust safe_set *)
      | Unset (Prod l) ->
         let k = mbind_assoc kprod v.uvar_arity l in
         safe_set_kuvar All v k os ; false (* FIXME: should not trust safe_set *)
    in
    let ul = List.filter fn (kuvar_list k) in
    let ol = ouvar_list k in
    let k = List.fold_left (fun acc (v,_) -> KKAll (bind_kuvar v acc)) k ul in
    let k = List.fold_left (fun acc v -> KOAll (bind_ouvar v acc)) k ol in
    (k, prf, calls)

let try_fold_def : kind -> kind = fun k ->
  let save_debug = !Io.debug in
  Io.debug := "";
  let match_def k def = (* TODO: share code with TMLet *)
    let kargs = Array.init def.tdef_karity (fun n -> new_kuvar ()) in
    let oargs = Array.init def.tdef_oarity (fun n -> new_ouvar ()) in
    let lkargs = List.map (function KUVar(u,_) -> u | _ -> assert false)
      (Array.to_list kargs) in
    let loargs = List.map (function OUVar(u,_) -> u | _ -> assert false)
      (Array.to_list oargs) in
    let k' = KDefi(def,oargs,kargs) in
    if match_kind lkargs loargs k' k then k' else raise Not_found;
  in
  let res =
    match repr k with
    | KDefi _ -> k
    | _ ->
       let defs = Hashtbl.fold (fun _ a l -> a::l) typ_env [] in
       let defs = List.sort
         (fun d1 d2 -> compare (d1.tdef_karity + d1.tdef_oarity)
                               (d2.tdef_karity + d2.tdef_oarity)) defs
       in
       let rec fn = function
         | [] -> k
         | def::l ->
            try
              match_def k def
            with
              Not_found -> fn l
       in
       fn defs
  in
  Io.debug := save_debug;
  res

let _ = Ast.ftry_fold_def := try_fold_def
