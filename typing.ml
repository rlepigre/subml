(****************************************************************************)
(**{3                   Typing and subtyping algorithms                    }*)
(****************************************************************************)
open Bindlib
open Ast
open Binding
open Print
open Pos
open Compare
open Term
open Generalise
open TypingBase
open Error
open LibTools

(** Result type of [check_rec]. *)
type ind =
  | Use of schema
  (** The given induction hypothesis applies. *)
  | New of (schema * kind * kind * (ordi * ordi) list) option
  (** The given induction hypothesis has been registered. *)

type subinfo =
  { left  : (string * kind) list
  ; right : (string * kind) list
  ; both  : string list
  }

let sempty = { left = []; right = []; both = [] }

type subctxt =
  | Free
  | SSum of subinfo
  | SPro of subinfo

let is_free sctxt = match sctxt with
  | Free -> true
  | SSum sc -> sc.left = []
  | SPro sc -> sc.right = []

let sc_of_pro sctxt = match sctxt with
  | SPro sc -> sc
  | Free -> sempty
  | _ -> assert false

let sc_of_sum sctxt = match sctxt with
  | SSum sc -> sc
  | Free -> sempty
  | _ -> assert false

(** [check_rec ctxt t a b] checks whether a given pointed subtyping relation
    can be derived in the current context using an induction hypothesis. If
    not, the current schema is registered as an induction hypothesis so that
    it can be used in a later call to [check_rec]. *)
let check_rec : subctxt -> ctxt -> term -> kind -> kind -> ind * ctxt
  = fun sctxt ctxt t a b ->
  (* HEURISTIC avoiding loops by unifying ordinal variables. When variables
     are kept, the program loops on useful examples. *)
  let _ =
    match (full_repr a, full_repr b) with
    | KFixM(o ,_), KFixM(o',_)
    | KFixN(o',_), KFixN(o ,_) -> ignore (eq_ordi ctxt.non_zero o o')
    | _                        -> ()
  in

  (* HEURISTIC obtained by trial and error. *)
  if sctxt <> Free || (
    (match a with
     | KFixM _ -> false
     | KFixN _ -> has_leading_exists a
     | _       -> true)
    &&
      (match b with
       | KFixM _ -> has_leading_forall b
       | KFixN _ -> false
       | _       -> true))
  then (New None, ctxt) else

  (* Actual start of the function. *)
  let _ = Io.log_ind "Adding IH %a < %a\n%!" Print.kind a Print.kind b in
  match generalise ctxt.non_zero (SchKind a) b ctxt.call_graphs with
  | None                  -> (New None, ctxt)
  | Some(new_sch, new_os) ->
      try
        (* Try to apply the induction hypothesis (need to find a previously
           encountered schema. *)
        Io.log_ind "Searching schema %a\n%!" (print_schema ~ord_name:"α") new_sch;
        let old_sch = List.find (eq_schema new_sch) ctxt.sub_ihs in
        Io.log_ind "Found schema     %a\n%!" (print_schema ~ord_name:"α") old_sch;
        add_call ctxt old_sch.sch_index new_os true;
        (Use old_sch, ctxt)
      with Not_found ->
        (* We cannot apply the induction hypothesis. However, we register
           our new schema as an induction hypothesis for later and
           build the new subtyping judgement we need to prove *)
        add_call ctxt new_sch.sch_index new_os false;
        let (os, non_zero, a, b) = recompose_kind ~general:false new_sch in
        let sub_ihs = new_sch :: ctxt.sub_ihs in
        let top_induction = (new_sch.sch_index, os) in
        let ctxt = { ctxt with sub_ihs ; non_zero ; top_induction } in
        Io.log_ind "Proving schema %a < %a\n%!" Print.kind a Print.kind b;
        (* Need the map table between the new and old ordinals, see below *)
        let fn (_,o1) (_,o2) =
          (o1, match o2 with OVari _ -> OConv | _ -> o2)
        in
        let tros = List.map2 fn os new_os in
        (New (Some (new_sch, a, b, tros)), ctxt)

let search_induction subtype prfptr ctxt t c hyps =
  (* Search for all the induction hypotheses that can be applied. *)
  Io.log_typ "searching IH (1):\n  %a %a\n%!" Print.kind c print_nz ctxt;
  let rec find_good_call = function
    | [] -> Io.log_ind "no induction hyp found\n%!";
            raise Not_found
    | sch::hyps ->
       let time = Timed.Time.save () in
       try
         let (ov, pos, _, a) = recompose sch in
         Io.log_ind "searching IH (2) with %d ~ %a <- %a:\n%!"
                    (Sct.int_of_index sch.sch_index) Print.kind a Print.kind c;
         (* We need to call [subtype] to rollback unification if it fails. *)
         let prf = subtype ctxt t a c in
         (* Change the proof even if wrong to have a good error message *)
         if !prfptr = Todo then Timed.(prfptr := Induction(sch,prf));
         check_sub_proof prf; (* NOTE: check for subtype error *)
         if not (List.for_all (is_positive ctxt.non_zero) pos) then raise Exit;
         Io.log_ind "induction hyp applies with %d %a ~ %a <- %a:\n%!"
                    (Sct.int_of_index sch.sch_index) Print.kind a Print.kind c
                    print_nz { ctxt with non_zero = pos};
         Sct.add_call ctxt.call_graphs (build_call ctxt sch.sch_index ov true);
         Timed.(prfptr := Induction(sch, prf))
       with Exit | Error _ -> Timed.Time.rollback time;
                              find_good_call hyps
  in
  find_good_call (List.rev hyps)

(* Check if the typing of a fixpoint comes from an induction hypothesis *)
let check_fix type_check subtype prfptr ctxt t manual depth f c =
  (* Stop if maximum depth has been reached. *)
  if depth < 0 then () else
  (* Obtain the relevant hypotheses (those which binder is the same). *)
  let (ctxt, hyps) =
    try (ctxt, List.assq f ctxt.fix_ihs) with Not_found ->
    let hyps = ref [] in
    let fix_ihs = (f, hyps) :: ctxt.fix_ihs in
    ({ctxt with fix_ihs}, hyps)
  in
  (* Search an induction hypothesis that can be applied. *)
  try
    search_induction subtype prfptr ctxt t c !hyps with Not_found ->
  (* There were no such induction hypothesis so we unroll the fixpoint. *)
  let manual = match manual with
    | None -> TypingBase.has_leading_ord_quantifier c
    | Some m -> m
  in
  let e = Pos.none (TFixY(Some manual,depth - 1, f)) in
  match generalise ~manual ctxt.non_zero (SchTerm f) c ctxt.call_graphs with
  | None          -> assert false (* FIXME why cannot fail ? *)
  | Some(sch, os) ->
      if os <> [] then Timed.(hyps := sch :: !hyps);
      let (os0, non_zero, _, a) = recompose_term ~general:false sch in
      let tros = List.combine (List.map snd os) (List.map snd os0) in
      Io.log_ind "Adding IH (1) %d:\n  %a => %a\n%!"
        (Sct.int_of_index sch.sch_index) Print.kind c Print.kind a;
      add_call ctxt sch.sch_index os false;
      let ctxt = {ctxt with top_induction = (sch.sch_index, os0); non_zero} in
      let prf = type_check ctxt (subst f e.elt) a in
      let prf = (ctxt.non_zero, e, a, Typ_Yufl prf) in
      Timed.(prfptr := Unroll(sch,tros, prf))


let print_sctxt ff sctxt =
  let fn ff = List.iter (fun (s,k) ->
                  Format.fprintf ff "(%s : %a) " s Print.kind k)
  in
  let gn ff =  List.iter (Format.fprintf ff "%s ")
  in
  match sctxt with
  | Free -> ()
  | SPro sc ->
     Format.fprintf ff "{ left = %a; both = %a; right = %a }\n"
                    fn sc.left gn sc.both fn sc.right
  | SSum sc ->
     Format.fprintf ff "[ left = %a; both = %a; right = %a ]\n"
                    fn sc.left gn sc.both fn sc.right

let rec subtype : subctxt -> ctxt -> term -> kind -> kind -> sub_prf
  = fun sctxt ctxt0 t0 a0 b0 ->
  Io.log_sub "%a%a  ∈ %a\n  ⊂ %a\n  %a\n\n%!" print_sctxt sctxt Print.term t0 Print.kind a0
    Print.kind b0 print_nz ctxt0;
  let a = full_repr a0 in
  let b = full_repr b0 in
  if is_free sctxt && eq_kind ctxt0.non_zero a b then
    (ctxt0.non_zero, t0, a0, b0, Sub_Lower)
  else try try
    let rule = match (a, b) with
    | (KMRec(ptr,a), _           ) ->
       Sub_And_l(subtype sctxt ctxt0 t0 a b0)

    | (_           , KNRec(ptr,b))->
       Sub_Or_r(subtype sctxt ctxt0 t0 a0 b)

    | (KNRec(ptr,a), KUVar _     )
        when Subset.test (eq_ordi ctxt0.non_zero) ptr ctxt0.non_zero ->
       Sub_Or_l(subtype sctxt ctxt0 t0 a b0)

    | (KUVar _     , KMRec(ptr,b))
        when Subset.test (eq_ordi ctxt0.non_zero) ptr ctxt0.non_zero ->
       Sub_And_r(subtype sctxt ctxt0 t0 a0 b)

    (* quantification rule introducing witness before induction *)
    | (_           , KKAll(f)    ) ->
        let p = subtype sctxt ctxt0 t0 a0 (subst f (KUCst(t0,f,true))) in
        Sub_KAll_r(p)

    | (KKExi(f)    , _           ) ->
        let p = subtype sctxt ctxt0 t0 (subst f (KECst(t0,f,true))) b0 in
        Sub_KExi_l(p)

    | (_           , KOAll(f)    ) ->
        let p = subtype sctxt ctxt0 t0 a0 (subst f (OLess(OMaxi, NotIn(t0,f)))) in
        Sub_OAll_r(p)

    | (KOExi(f)    , _           ) ->
        let p = subtype sctxt ctxt0 t0 (subst f (OLess(OMaxi, In(t0,f)))) b0 in
        Sub_OExi_l(p)

    (* Handling of unification variables, same variable different
       parameters: keep the common one only. *)
    | (KUVar(ua,osa),KUVar(ub,osb)) when eq_uvar ua ub && is_free sctxt ->
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
         let f = unbox (mbind mk_free_o (Array.make ua.uvar_arity "α") (fun x ->
           box_apply (fun os -> KUVar(u,os)) (box_array (Array.init new_len (fun i ->
             x.(os.(i)))))))
         in
         if is_unset ua then safe_set_kuvar sNeg ua f osa);
       let (_,_,_,_,r) = subtype sctxt ctxt0 t0 a0 b0 in r

    | (KUVar(ua,osa),KUVar(ub,osb)) when is_free sctxt ->
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
       let u = new_kuvara new_len in
       let k = KUVar(u,os) in
       (* NOTE: the call to  bind_fn above may (very rarely) instanciate
                  ua or ub, so we added a test to avoid an assert false  *)
       if is_unset ua then
         safe_set_kuvar sNeg ua (bind_ordis osa k) osa;
       if is_unset ub then
         safe_set_kuvar sPos ub (bind_ordis osb k) osb;
       let (_,_,_,_,r) = subtype sctxt ctxt0 t0 a0 b0 in r

    | (KUVar(ua,os), b            ) when
           (match sctxt with SSum sc -> sc.left = [] | _ -> true) ->
       let b' = match sctxt with
         | Free -> b0
         | SPro sc ->  (* TODO: b0 without sc.both *)
            List.fold_left (fun acc (s, k) ->
                KProd(s,k,acc)) b0 sc.right
         | SSum sc ->  (* TODO: delay *)
            let ls = List.filter (fun (_,k) -> kuvar_occur ua k = Non) sc.right in
            List.fold_left (fun acc (s, k) -> KDSum(s,k,acc)) b0 ls
       in
       let bb = bind_ordis os b' in
       if is_unset ua then safe_set_kuvar sNeg ua bb os;
       let (_,_,_,_,r) = subtype sctxt ctxt0 t0 a0 b0 in r

    | (a           , KUVar(ub,os)) when
           (match sctxt with SPro sc -> sc.right = [] | _ -> true) ->
       let a' = match sctxt with
         | Free -> a0
         | SPro sc -> (* TODO: delay *)
            let ls = List.filter (fun (_,k) -> kuvar_occur ub k = Non) sc.left in
            List.fold_left (fun acc (s, k) ->
                KProd(s,k,acc)) a0 ls
         | SSum sc -> (* TODO: a0 without sc.both *)
            List.fold_left (fun acc (s, k) ->
                KDSum(s,k,acc)) a0 sc.left
       in
       let aa = bind_ordis os a' in
       if is_unset ub then safe_set_kuvar sPos ub aa os;
       let (_,_,_,_,r) = subtype sctxt ctxt0 t0 a0 b0 in r

    | _ -> raise Exit
  in (ctxt0.non_zero, t0, a0, b0, rule)
  with Exit ->
  let (ind_res, ctxt) = check_rec sctxt ctxt0 t0 a b in
  match ind_res with
  | Use schema  -> (ctxt.non_zero, t0, a0, b0, Sub_Ind schema)
  | New ind_ref ->
  let (finalise_proof,t,a,b,a0,b0) = match ind_ref with
    | None -> ((fun x -> x),t0,a,b,a0,b0)
    | Some(n,a,b,tros) ->
       let a = full_repr a and b = full_repr b in
       let t1 = unbox (generic_tcnst (box a) (box b)) in
       ((fun x -> ctxt0.non_zero,t0,a0,b0,Sub_Gen(n, tros, x)),
        t1, a, b, a, b)
  in
  let rule =
    match (a,b) with
    (* Arrow type. *)
    | (KFunc(a1,b1), KFunc(a2,b2)) when sctxt = Free ->
       let wit =
         let f x = tappl None (box t) (box_apply Pos.none x) in
         let bnd = unbox (bind mk_free_tvari "x" f) in
         unbox (tcnst bnd (box a2) (box b2))
       in
        (* NOTE: the heuristic below works well for Church like encoding *)
       if has_uvar b1 then
         let wit =
           if strict_eq_kind a2 KUnit then tunit
           else wit
         in
         let p2 = subtype Free ctxt (Pos.none (TAppl(t, wit))) b1 b2 in
         let p1 = subtype Free ctxt wit a2 a1 in
         Sub_Func(p1, p2)
       else
         let p1 = subtype Free ctxt wit a2 a1 in
         let wit =
           if strict_eq_kind a2 KUnit then tunit
           else wit
         in
         let p2 = subtype Free ctxt (Pos.none (TAppl(t, wit))) b1 b2 in
         Sub_Func(p1, p2)

    | (KUnit, KUnit) ->
       begin
         match sctxt with
         | SPro sc ->
            let l  = List.map fst sc.right in
            let ls = String.concat ", " l in
            if l <> [] then subtype_error ("Product field clash: " ^ ls);
            Sub_Lower
         | SSum _ ->
            subtype_error ("Mixing sums and product")
         | _ -> Sub_Lower
       end

    | (KZero, KZero) ->
       begin
         match sctxt with
         | SSum sc ->
            let l  = List.map fst sc.left in
            let ls = String.concat ", " l in
            if l <> [] then subtype_error ("Varant clash: " ^ ls);
            Sub_Lower
         | SPro _ ->
            subtype_error ("Mixing sums and product")
         | _ -> Sub_Lower
       end

    (* μl and νr rules. *)
    | (_           , KFixN(o,f)  ) ->
        let o', ctxt =
          match orepr o with
          | OSucc o' -> o', ctxt
          | o ->
             let g = bind mk_free_o (binder_name f) (fun o ->
               bind_apply (Bindlib.box f) (box_apply (fun o -> KFixN(o,f)) o))
             in
             let o' = opred o (NotIn(t,unbox g)) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi false) o' (print_ordi false) o;
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi true) o' (print_ordi true) o;
        let cst = KFixN(o', f) in
        let prf = subtype sctxt ctxt t a0 (subst f cst) in
        Sub_FixN_r prf

    | (KFixM(o,f)   , _          ) ->
        let o', ctxt =
          match orepr o with
          | OSucc o' -> o', ctxt
          | o ->
             let g = bind mk_free_o (binder_name f) (fun o ->
               bind_apply (Bindlib.box f) (box_apply (fun o -> KFixM(o,f)) o))
             in
             let o' = opred o (In(t,unbox g)) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi false) o' (print_ordi false) o;
        Io.log_sub "creating %a < %a\n%!"
          (print_ordi true) o' (print_ordi true) o;
        let cst = KFixM(o', f) in
        let prf = subtype sctxt ctxt t (subst f cst) b0 in
        Sub_FixM_l prf

    (* μr and νl rules. *)
    | (KFixN(o,f)  , _           ) ->
       let o' = try
           ofindpred ctxt o
         with Not_found ->
           subtype_error "Subtyping clash (no rule apply for left nu)."
       in
       let a = if o' = OConv then a else KFixN(o',f) in
       let p = subtype sctxt ctxt t (subst f a) b0 in
       Sub_FixN_l(p)

    | (_           , KFixM(o,f)  ) ->
       let o' = try
           ofindpred ctxt o
         with Not_found ->
           subtype_error "Subtyping clash (no rule apply for right mu)."
       in
       let b = if o' = OConv then b else KFixM(o',f) in
       let p = subtype sctxt ctxt t a0 (subst f b) in
       Sub_FixM_r(p)

    (* quantification rule introducing unification variable last *)
    | (KKAll(f)    , _           ) ->
        let p = subtype sctxt ctxt t (subst f (new_kuvar ())) b0 in
        Sub_KAll_l(p)

    | (_           , KKExi(f)    ) ->
        let p = subtype sctxt ctxt t a0 (subst f (new_kuvar ())) in
        Sub_KExi_r(p)

    | (KOAll(f)    , _           ) ->
       let p = subtype sctxt ctxt t (subst f (new_ouvar ())) b0 in
       Sub_OAll_l(p)

    | (_           , KOExi(f)    ) ->
        let p = subtype sctxt ctxt t a0 (subst f (new_ouvar ())) in
        Sub_OExi_r(p)

    | (KNRec(ptr, a), _          )
        when Subset.test (eq_ordi ctxt.non_zero) ptr ctxt.non_zero ->
       Sub_Or_l(subtype sctxt ctxt t a b0)

    | (_           , KMRec(ptr, b))
        when Subset.test (eq_ordi ctxt.non_zero) ptr ctxt.non_zero ->
       Sub_And_r(subtype sctxt ctxt t a0 b)

    | (KProd(s,a,e), _) when (match sctxt with SSum _ -> false | _ -> true) ->
       let sc = sc_of_pro sctxt in
       if List.mem s sc.both then Sub_Prod(None, subtype sctxt ctxt t0 e b)
       else
         begin
           try
             let b' = List.assoc s sc.right in
             let sctxt = SPro { sc with both = s::sc.both
                                      ; right = rem_assoc s sc.right }
             in
             Sub_Prod(Some (subtype Free ctxt t0 a b'),
                            subtype sctxt ctxt t0 e b)
           with
             Not_found ->
             let sctxt = SPro { sc with left = (s,a)::sc.left } in
             Sub_Prod(None,subtype sctxt ctxt t0 e b)
         end

    | (_, KProd(s,b,e)) when (match sctxt with SSum _ -> false | _ -> true) ->
       let sc = sc_of_pro sctxt in
       if List.mem s sc.both then Sub_Prod(None, subtype sctxt ctxt t0 a e)
       else
         begin
           try
             let a' = List.assoc s sc.left in
             let sctxt = SPro { sc with both = s::sc.both
                                       ; left = rem_assoc s sc.left }
             in
             Sub_Prod(Some(subtype Free ctxt t0 a' b),
                           subtype sctxt ctxt t0 a e)
           with
             Not_found ->
             let sctxt = SPro { sc with right = (s,b)::sc.right } in
             Sub_Prod(None,subtype sctxt ctxt t0 a e)
         end

    | (KDSum(s,a,e), _) when (match sctxt with SPro _ -> false | _ -> true) ->
       let sc = sc_of_sum sctxt in
       if List.mem s sc.both then Sub_DSum(None,subtype sctxt ctxt t0 e b)
       else
         begin
           try
             let b' = List.assoc s sc.right in
             let sctxt = SSum { sc with both = s::sc.both
                                      ; right = rem_assoc s sc.right }
             in
             Sub_DSum(Some(subtype Free ctxt t0 a b'),
                           subtype sctxt ctxt t0 e b)
           with
             Not_found ->
             let sctxt = SSum { sc with left = (s,a)::sc.left } in
             Sub_DSum(None,subtype sctxt ctxt t0 e b)
         end

    | (_, KDSum(s,b,e)) when (match sctxt with SPro _ -> false | _ -> true) ->
       let sc = sc_of_sum sctxt in
       if List.mem s sc.both then Sub_DSum(None, subtype sctxt ctxt t0 a e) (* FIXME *)
       else
         begin
           try
             let a' = List.assoc s sc.left in
             let sctxt = SSum { sc with both = s::sc.both
                                      ; left = rem_assoc s sc.left }
             in
             Sub_DSum(Some(subtype Free ctxt t0 a' b),
                           subtype sctxt ctxt t0 a e)
           with
             Not_found ->
             let sctxt = SSum { sc with right = (s,b)::sc.right } in
             Sub_DSum(None,subtype sctxt ctxt t0 a e) (* FIXME *)
         end

    (* Subtype clash. *)
    | (_           , _           ) ->
       subtype_error "Subtyping clash (no rule apply)."
  in
  finalise_proof (ctxt.non_zero, t, a0, b0, rule)
  with
  | Subtype_error e -> (ctxt0.non_zero, t0, a0, b0, Sub_Error e)
  | Occur_check     -> (ctxt0.non_zero, t0, a0, b0, Sub_Error "Occur_check")

(** A boolean test for subtyping *)
let is_subtype ctxt t a b =
  Timed.pure_test (fun () ->
    (** protect the call graph, because we don't need the proof we only
        want to instantiate some unification variables *)
    let ctxt = { ctxt with call_graphs = Sct.copy ctxt.call_graphs} in
    let prf = subtype Free ctxt t a b in
    try check_sub_proof prf; true with Error _ -> false) ()

let rec type_check : ctxt -> term -> kind -> typ_prf = fun ctxt t c ->
  let c = repr c in
  Io.log_typ "%a :\n  %a\n  %a\n\n%!" Print.term t Print.kind c print_nz ctxt;
  let r =
    try
      match t.elt with
      | TCoer(t,a) ->
         let p1 = subtype Free ctxt t a c in
         let p2 = type_check ctxt t a in
         Typ_Coer(p1, p2)
      | TMLet(bk,x,bt) ->
         let kx =
           match x with
           | None                       -> c
           | Some({elt = TCnst(_,c,_)}) -> c
           | Some({elt = TDefi(d)})     -> d.ttype
           (* NOTE other cases not allowed by parser *)
           | Some(_)                    -> assert false
         in
         let (oa, ka) = mmbinder_arities bk odummy in
         assert((oa, ka) = mmbinder_arities bt odummy);
         let oargs = Array.init oa (fun _ -> new_ouvar ()) in
         let kargs = Array.init ka (fun _ -> new_kuvar ()) in
         let k = mmsubst bk oargs kargs in
         let t = mmsubst bt oargs kargs in
         if is_subtype ctxt (from_opt x t) kx k then
           let p = type_check ctxt t c in
           Typ_Nope(p)
         else
           type_error "Type matching failed"
      | TAbst(ao,f,_) ->
         let a = from_opt' ao new_kuvar in
         let b = new_kuvar () in
         let ptr = Subset.create ctxt.non_zero in
         let c' = KNRec(ptr,KFunc(a,b)) in
         let p1 = subtype Free ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let wit = unbox (tcnst f (box a) (box b)) in
         let p2 = type_check ctxt (subst f wit.elt) b in
         Typ_Func_i(p1, p2)
      | TAppl(f,u) when is_neutral f && not (is_neutral u)->
         let a = if strict_eq_term u tunit then KUnit else new_kuvar () in
         let ptr = Subset.create ctxt.non_zero in
         let p2 = type_check ctxt f (KMRec(ptr,KFunc(a,c))) in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let p1 = type_check ctxt u a in
         Typ_Func_e(p1, p2)
      | TAppl(t,u) ->
         let a = if strict_eq_term u tunit then KUnit else new_kuvar () in
         let p1 = type_check ctxt u a in
         let p2 = type_check ctxt t (KFunc(a,c)) in
         Typ_Func_e(p1, p2)
      | TReco(fs) ->
         let ts = List.map (fun (l,_) -> (l, new_kuvar ())) fs in
         let c' = List.fold_left (fun acc (l,k) -> KProd(l, k, acc)) KUnit ts in
         let ptr = Subset.create ctxt.non_zero in
         let c' =  if is_normal t then KNRec(ptr,c') else c' in
         let p1 = subtype Free ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let check (l,t) = type_check ctxt t (List.assoc l ts) in
         let p2s = List.map check fs in
         Typ_Prod_i(p1, p2s)
      | TProj(t,l) ->
         let c' = KProd(l, c, new_kuvar ()) in
         let p = type_check ctxt t c' in
         Typ_Prod_e(p)
      | TCons(d,v) ->
         let a = new_kuvar () in
         let c' = KDSum(d, a, new_kuvar ()) in
         let ptr = Subset.create ctxt.non_zero in
         let c' = if is_normal t then KNRec(ptr,c') else c' in
         let p1 = subtype Free ctxt t c' c in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let p2 = type_check ctxt v a in
         Typ_DSum_i(p1, p2)
      | TCase(t,l,d) ->
         let k0 = match d with
           | None -> KZero
           | Some t -> new_kuvar ()
         in
         let f (c,t) =
           let k = match t.elt with TAbst(Some k, _, _) -> k
                                  | _ -> new_kuvar ()
           in
           (c,k)
         in
         let ts = List.map f l in
         let k = List.fold_left (fun acc (l,k) -> KDSum(l, k, acc)) k0 ts in
         let ptr = Subset.create ctxt.non_zero in
         let p1 = type_check ctxt t (KMRec(ptr,k)) in
         let ctxt = add_positives ctxt (Subset.get ptr) in
         let check (d,f) =
           let cc = List.assoc d ts in
           type_check ctxt f (KFunc(cc,c))
         in
         let p2s = List.map check l in
         let p3 =
           match d with
           | None -> None
           | Some f ->
              Some (type_check ctxt f (KFunc(k0,c)))
         in
         Typ_DSum_e(p1, p2s, p3)
      | TDefi(v) ->
         let p = subtype Free ctxt v.value v.ttype c in
         Typ_Defi(p)
      | TPrnt(_) ->
         let p = subtype Free ctxt t KUnit c in
         Typ_Prnt(p)
      | TFixY(manual,depth,f) ->
         let prf = ref Todo in
         let check () = check_fix type_check (subtype Free) prf ctxt t manual depth f c in
         Timed.(ctxt.fix_todo := check :: !(ctxt.fix_todo));
         Typ_YGen prf
      | TCnst(_,a,b) ->
         let p = subtype Free ctxt t a c in
         Typ_Cnst(p)
      | TAbrt        ->
         Typ_Abrt
      | TCaco        ->
         let a = new_kuvar () in
         let b = new_kuvar () in
         let peirce = KFunc(KFunc(KFunc(a,b),a),a) in
         let _p = subtype Free ctxt t peirce c in
         Typ_Abrt (* FIXME *)
      | TVari _ | TVars _ | TStck _ -> assert false
    with
    | Subtype_error msg (* FIXME: could we avoid Subtype_error in typing.
                           It not, should use the same exception *)
    | Type_error msg -> Typ_Error msg
    | Occur_check    -> Typ_Error "occur_check"
    | Sys.Break      -> Typ_Error "interrupted"
  in (ctxt.non_zero, t, c, r)

(** [subtype t a b] checks the pointed subtyping relation "t ∈ A ⊂ B". Since
    the term [t] is optional, a generic witness is used when [t = None]. The
    function returns a subtyping proof together with the successful instance
    of the SCT. *)
let subtype : term option -> kind -> kind -> sub_prf * Sct.t = fun t a b ->
  let t = from_opt t (unbox (generic_tcnst (box a) (box b))) in
  let ctxt = empty_ctxt () in
  try
    let p = subtype Free ctxt t a b in
    let call_graphs = Sct.inline ctxt.call_graphs in
    if not (Sct.sct call_graphs) then loop_error None;
    check_sub_proof p;
    reset_all ();
    (p, call_graphs)
  with e -> reset_all (); raise e

(** [type_check t ko] type-checks the term [t] against the optional type [k]
    (or a unification variable). The function returns a type for [t] and the
    corresponding typing proof and successful instance of the SCT. When the
    function is called with [ko = Some k], the returned type is [k]. *)
let type_check : term -> kind option -> kind * typ_prf * Sct.t = fun t k ->
  let k = from_opt' k new_kuvar in
  let ctxt = empty_ctxt () in
  let (prf, calls) =
    try
      let p = type_check ctxt t k in
      run_fix_todo ctxt;
      check_typ_proof p;
      let call_graphs = Sct.inline ctxt.call_graphs in
      if not (Sct.sct call_graphs) then loop_error t.pos;
      reset_all ();
      (p, call_graphs)
    with e -> reset_all (); raise e
  in
  (* Generalisation. *)
  let fn (v, os) = is_unset v in
  let kvs = List.filter fn (kuvar_list k) in
  let ovs = ouvar_list k in
  let kfn acc v = KKAll (bind_kuvar (fst v) acc) in
  let ofn acc v = KOAll (bind_ouvar v acc) in
  (List.fold_left ofn (List.fold_left kfn k kvs) ovs, prf, calls)
