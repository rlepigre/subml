open Bindlib
open Ast
open Print
open Sct
open Position
open Compare
open Type

exception Type_error of pos * string
let type_error : pos -> string -> 'a =
  fun p msg -> raise (Type_error(p,msg))

exception Subtype_error of string
let subtype_error : string -> 'a =
  fun msg -> raise (Subtype_error msg)

type subtype_ctxt =
  { induction_hyp     : (int * induction_type * (int * ordinal) list) list
  ; calls             : pre_calls ref
  ; delayed           : (unit -> unit) list ref
  ; positive_ordinals : (ordinal * ordinal) list }

and induction_type =
  | Sub of int list * kind * kind
  | Rec of (term,term) binder * kind * kind

let empty_ctxt () =
  { induction_hyp = []
  ; calls = ref []
  ; delayed = ref []
  ; positive_ordinals = [] }

let find_indexes pos index index' a b =
  Io.log_mat "build matrix for %d %d\n" index index';
  let c = Sct.arity index and l = Sct.arity index' in
  let m = Array.init l (fun _ -> Array.make c Unknown) in
  let pos = List.map fst pos in
  List.iter (fun (j,o') ->
    List.iter (fun (i,o) ->
      Io.log_mat "  compare %d %a <=? %d %a => %!" i (print_ordinal false) o
        j (print_ordinal false) o';
      let r =
        if less_ordinal pos o o' then Less
        else if leq_ordinal pos o o' then Leq
        else Unknown
      in
      Io.log_mat "%a\n%!" print_cmp r;
      m.(j).(i) <- r
    ) a) b;
  m

let rec find_positive ctxt o =
  let o = orepr o in
  (*  Io.log "find positive %a\n%!" (print_ordinal false) o;*)
  match o with
  | OConv -> OConv
  | OSucc o' -> o'
  | OUVar(p) ->
     let o' = OUVar(ref None) in
     set_ouvar p (OSucc o'); o'
  | _ ->
    assoc_ordinal o ctxt.positive_ordinals

(* FIXME: the function below are certainly missing cases *)
let rec with_clause a (s,b) = match full_repr a with
  | KKExi(f) ->
     if binder_name f = s then subst f b else begin
       KKExi(binder_from_fun (binder_name f) (fun x ->
         with_clause (subst f x) (s,b)))
     end
  | KFixM(OConv,f) -> with_clause (subst f (KFixM(OConv,f))) (s,b)
  | KFixN(OConv,f) -> with_clause (subst f (KFixN(OConv,f))) (s,b)
  | k       ->
     Io.log "KWith constraint on %s in %a\n%!" s (print_kind false) k;
     subtype_error ("Illegal use of \"with\" on variable "^s^".")

let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f) in
     if binder_name f = s then c else dot_proj t (subst f c) s
  | KWith(k,(s',a)) ->
     if s' = s then a else dot_proj t (with_clause k (s',a)) s
  | k ->
     raise Not_found

let rec lambda_kind t k s = match full_repr k with
  | KKAll(f) ->
     let c = KUCst(t,f) in
     if binder_name f = s then c else lambda_kind t (subst f c) s
  (* FIXME KOAll *)
  | _ -> subtype_error ("can't find for all "^s)

let rec lambda_ordinal t k s =
  match full_repr k with
  | KOAll(f) ->
     let c = OLess(OConv,NotIn(t,f)) in
     if binder_name f = s then c else lambda_ordinal t (subst f c) s
  (* FIXME KKAll *)
  | _ -> subtype_error ("can't find for all (ord) "^s)

let has_leading_exists : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(a,b) -> fn b
    | KProd(ls)
    | KDSum(ls)  -> List.exists (fun (l,a) -> fn a) ls
    | KKExi(f)   -> true
    | KOExi(f)   -> fn (subst f (OTInt(-73)))
    | KWith(k,s) -> true
    | _ -> false
  in
  fn k

let has_uvar : kind -> bool = fun k ->
  let rec fn k =
    match repr k with
    | KFunc(a,b) -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)  -> List.iter (fun (l,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)   -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f) -> gn o; fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)   -> fn (subst f (OTInt(-42)))
    | KUVar(u)   -> raise Exit
    | KDefi(d,o,a) -> Array.iter gn o; Array.iter fn a
    | KWith(k,c) -> let (_,b) = c in fn k; fn b
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
    | t          -> ()
  and gn o =
    match orepr o with
    | OUVar _ -> raise Exit
    | _       -> ()
  in
  try
    fn k; false
  with
    Exit -> true

let kuvar_list : kind -> kuvar list = fun k ->
  let r = ref [] in
  let rec fn k =
    match repr k with
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f (OTInt(-42)))
    | KUVar(u)     -> if not (List.exists (eq_kuvar u) !r) then r := u :: !r
    | KDefi(d,_,a) -> Array.iter fn a
    | KWith(k,c)   -> fn k; fn (snd c)
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
    | _            -> ()
  in
  fn k; !r

let ouvar_list : kind -> ouvar list = fun k ->
  let r = ref [] in
  let rec fn k =
    match repr k with
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> gn o; fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f (OTInt(-42)))
    | KDefi(d,o,a) -> Array.iter gn o;  Array.iter fn a
    | KWith(k,c)   -> fn k; fn (snd c)
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
    | _            -> ()
  and gn o =
    match orepr o with
    | OSucc(o) -> gn o
    | OUVar(v) -> if not (List.exists (eq_ouvar v) !r) then r := v :: !r
    | _        -> ()
  in
  fn k; !r

(* FIXME: end of the function which certainly miss cases *)

let cr = ref 0

let add_pos positives o o' =
  let o = orepr o in
  match o with
  | OConv | OSucc _ -> positives
  | _ ->
    (*  if List.exists (fun (o',_) -> eq_ordinal o o') positives then positives else*)
    (o, o') :: List.filter (fun (o',_) -> not (eq_ordinal o o')) positives

let add_positive ctxt o o' =
  { ctxt with positive_ordinals = add_pos ctxt.positive_ordinals o o' }

let add_positives ctxt gamma =
  let positive_ordinals =
    List.fold_left (fun positives (o, o') -> add_pos positives o o')
      ctxt.positive_ordinals gamma
  in
  { ctxt with positive_ordinals }

exception Induction_hyp of int

(* The boolean is true if we can apply the induction hypothesis. *)
let check_rec : term -> subtype_ctxt -> kind -> kind -> int option * int option * subtype_ctxt =
  fun t ctxt a b ->
    (* the test (has_uvar a || has_uvar b) is important to
       - avoid occur chek for induction variable
       - to keep the invariant that no ordinal <> OConv occur in
       positive mus and negative nus *)
    (* has_leading_exists, is to keep maximum information about
       existential witnesses otherwise some dot projection fail *)
    try
      if (has_uvar a || has_uvar b || has_leading_exists a) &&
        (match a with KFixM _ -> false | _ -> true) &&
        (match b with KFixN _ -> false | _ -> true)
      then raise Exit;
      (match a with MuRec _ | NuRec _ -> raise Exit | _ -> ());
      (match b with MuRec _ | NuRec _ -> raise Exit | _ -> ());
      let (a', b', os) = decompose Pos a b in
      let p' =
        let l =
          List.filter (fun (i,o) -> List.exists (fun (o',_) -> eq_ordinal o o')
            ctxt.positive_ordinals) os
        in
        List.sort compare (List.map fst l)
      in
      (*Io.log "\n\nIND len(os) = %d\n%!" (List.length os);
        Io.log "IND (%a < %a)\n%!" (print_kind false) a' (print_kind false) b';*)
      let pos = ctxt.positive_ordinals in
      List.iter (function (_,Rec _,_) -> () | (index,Sub(p0,a0,b0),os0) ->
        if Timed.pure_test (fun () -> p' = p0 && eq_kind a' a0 && eq_kind b0 b') () then (
          assert (List.length os = Sct.arity index);
          match ctxt.induction_hyp with
          | (index',_,os')::_ ->
             Io.log_sub "By induction\n\n%!";
             Timed.(ctxt.delayed := (fun () ->
               let m = find_indexes pos index index' os os' in
               ctxt.calls := (index, index', m, true) :: !(ctxt.calls)) :: !(ctxt.delayed));
             raise (Induction_hyp index)
          | _ -> assert false
        )) ctxt.induction_hyp;
      let fnum = new_function "S" (List.map Latex.ordinal_to_printer os) in
      (match ctxt.induction_hyp with
      | (index',_,os')::_ ->
           Timed.(ctxt.delayed := (fun () ->
             let m = find_indexes pos fnum index' os os' in
             ctxt.calls := (fnum, index', m, false) :: !(ctxt.calls)) :: !(ctxt.delayed));
      | _ -> ());
      let ctxt = { ctxt with
                   induction_hyp = (fnum, Sub(p', a', b'), os)::ctxt.induction_hyp }
      in
      (Some fnum, None, ctxt)
    with Exit -> (None, None, ctxt)
       | Induction_hyp n -> (None, Some n, ctxt)

let fixpoint_depth = ref 3

let print_positives ff ctxt =
  let p_aux ch (o1,o2) = Format.fprintf ff "%a < %a"
    (print_ordinal false) o2 (print_ordinal false) o1
  in
  match ctxt.positive_ordinals with
      | [] -> ()
      | l -> Io.log "  (%a)\n\n%!" (print_list p_aux ", ") l

let rec subtype : subtype_ctxt -> term -> kind -> kind -> sub_prf = fun ctxt t a0 b0 ->
  let a = full_repr a0 in
  let b = full_repr b0 in
  Io.log_sub "%a\n  ∈ %a\n  ⊂ %a\n  %a\n\n%!"
    (print_term false) t (print_kind false) a (print_kind false) b
    print_positives ctxt;
  if eq_kind a b then (t, a0, b0, None, Sub_Lower) else
  let (ind_ref, ind_hyp, ctxt) = check_rec t ctxt a b in
  let r = (* FIXME: le témoin n'est pas le bon *)
    match ind_hyp with
    | Some n -> Sub_Ind n
    | _ ->
    match (a,b) with
    | (MuRec(ptr,a), _           ) ->
       Sub_FixM_l(subtype ctxt t a b0)

    | (_           , NuRec(ptr,b))->
       Sub_FixN_r(subtype ctxt t a0 b)

    | (NuRec(ptr,a), KUVar _     )
        when Refinter.subset eq_ordinal ptr ctxt.positive_ordinals ->
       Sub_FixM_l(subtype ctxt t a b0)

    | (KUVar _     , MuRec(ptr,b))
        when Refinter.subset eq_ordinal ptr ctxt.positive_ordinals ->
       Sub_FixN_r(subtype ctxt t a0 b)

    (* unification. (sum and product special) *)
    | (KUVar(ua)   , KProd(l))
       when (match !(ua.kuvar_state) with Sum _ -> false | _ -> true) ->
       let l0 = match !(ua.kuvar_state) with
           Free -> []
         | Prod l -> l
         | Sum _ -> assert false
       in
       let l1 = ref l0 in
       List.iter (fun (s,k) ->
         try
           let _ = subtype ctxt t (List.assoc s l0) k  in
         (* FIXME: témoin et preuve *)
           ()
         with
           Not_found -> l1 := (s,k)::!l1) l;
       Timed.(ua.kuvar_state := Prod !l1);
       Sub_Lower

    | (KDSum(l)   , KUVar(ub)   )
       when (match !(ub.kuvar_state) with Prod _ -> false | _ -> true) ->
       let l0 = match !(ub.kuvar_state) with
           Free -> []
         | Sum l -> l
         | Prod _ -> assert false
       in
       let l1 = ref l0 in
       List.iter (fun (s,k) ->
         try
           let _ = subtype ctxt t k (List.assoc s l0)  in
         (* FIXME: témoin et preuve *)
           ()
         with
           Not_found -> l1 := (s,k)::!l1) l;
       Timed.(ub.kuvar_state := Sum !l1);
       Sub_Lower

    (* Handling of unification variables (immitation). *)
    | ((KUVar ua as a),(KUVar ub as b)) ->
        if !(ua.kuvar_state) = Free then set_kuvar true ua b
        else set_kuvar false ub a;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in r

    | (KUVar ua, b            ) ->
        set_kuvar true ua b0;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in r

    | (a           ,(KUVar ub))  ->
        set_kuvar false ub a0;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in r

    (* Arrow type. *)
    | (KFunc(a1,b1), KFunc(a2,b2)) ->
        let f x = tappl dummy_position (box t) x in
        let bnd = unbox (bind (tvari_p dummy_position) "x" f) in
        let wit = tcnst bnd a2 b2 in
        if has_uvar b1 then
          let p2 = subtype ctxt (dummy_pos (TAppl(t,wit))) b1 b2 in
          let p1 = subtype ctxt wit a2 a1 in
          Sub_Func(p1, p2)
        else
          let p1 = subtype ctxt wit a2 a1 in
          let p2 = subtype ctxt (dummy_pos (TAppl(t,wit))) b1 b2 in
          Sub_Func(p1, p2)

    (* Product type. *)
    | (KProd(fsa)  , KProd(fsb)  ) ->
        let check_field (l,b) =
          let a =
            try List.assoc l fsa
            with Not_found -> subtype_error ("Product fields clash: " ^ l)
          in
          subtype ctxt (dummy_pos (TProj(t,l))) a b
        in
        let ps = List.map check_field fsb in
        Sub_Prod(ps)

    (* Sum type. *)
    | (KDSum(csa)  , KDSum(csb)  ) ->
        let check_variant (c,a) =
          let t = unbox (tcase dummy_position (box t) [(c, idt)]) in
          let b =
            try List.assoc c csb
            with Not_found -> subtype_error ("Constructor clash: " ^ c)
          in
          subtype ctxt t a b
        in
        let ps = List.map check_variant csa in
        Sub_DSum(ps)

    (* Dot projection. *)
    | (KDPrj(t0,s) , _           ) ->
        let u = new_uvar () in
        let p1 = type_check ctxt t0 u in
        let p2 = subtype ctxt t (dot_proj t0 u s) b0 in
        Sub_DPrj_l(p1, p2)

    | (_           , KDPrj(t0,s) ) ->
        let u = new_uvar () in
        let p1 = type_check ctxt t0 u in
        let p2 = subtype ctxt t a0 (dot_proj t0 u s) in
        Sub_DPrj_r(p1, p2)

    (* KWith clause. *)
    | (KWith(a,e)  , _           ) ->
        let p = subtype ctxt t (with_clause a e) b0 in
        Sub_With_l(p)

    | (_           , KWith(b,e)  ) ->
        let p = subtype ctxt t a0 (with_clause b e) in
        Sub_With_r(p)

    (* Universal quantification over kinds. *)
    | (_           , KKAll(f)    ) ->
        let p = subtype ctxt t a0 (subst f (KUCst(t,f))) in
        Sub_KAll_r(p)

    | (KKAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (new_uvar ())) b0 in
        Sub_KAll_l(p)

    (* Existantial quantification over kinds. *)
    | (KKExi(f)    , _           ) ->
        let p = subtype ctxt t (subst f (KECst(t,f))) b0 in
        Sub_KExi_l(p)

    | (_           , KKExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (new_uvar ())) in
        Sub_KExi_r(p)

    (* Universal quantification over ordinals. *)
    | (_           , KOAll(f)    ) ->
        let p = subtype ctxt t a0 (subst f (OLess(OConv,NotIn(t,f)))) in
        Sub_OAll_r(p)

    | (KOAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (OUVar(ref None))) b0 in
        Sub_OAll_l(p)

    (* Existantial quantification over ordinals. *)
    | (KOExi(f)    , _           ) ->
        let p = subtype ctxt t (subst f (OLess(OConv,In(t,f)))) b0 in
        Sub_OExi_l(p)

    | (_           , KOExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (OUVar(ref None))) in
        Sub_OExi_r(p)

    (* μl and νr rules. *)
    | (_           , KFixN(o,f)  ) ->
        begin
          match a with
          | KFixN(o',_) -> let os = List.map fst ctxt.positive_ordinals in
                           ignore (Timed.pure_test (leq_ordinal os o) o')
          | _           -> ()
        end;
        let g = bind mk_free_ovari (binder_name f) (fun o ->
          bind_apply (Bindlib.box f) (box_apply (fun o -> KFixN(o,f)) o))
        in
        let o' = oless o (NotIn(t,unbox g)) in
        let ctxt = add_positive ctxt o o' in
        Io.log_sub "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        let cst = KFixN(o', f) in
        let prf = subtype ctxt t a0 (subst f cst) in
        Sub_FixN_r prf

    | (KFixM(o,f)   , _           ) ->
        begin
          match b with
          | KFixM(o',_) -> let os = List.map fst ctxt.positive_ordinals in
                           ignore (Timed.pure_test (leq_ordinal os o) o')
          | _           -> ()
        end;
        let g = bind mk_free_ovari (binder_name f) (fun o ->
          bind_apply (Bindlib.box f) (box_apply (fun o -> KFixM(o,f)) o))
        in
        let o' = oless o (In(t,unbox g)) in
        let ctxt = add_positive ctxt o o' in
        Io.log_sub "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        let cst = KFixM(o', f) in
        let prf = subtype ctxt t (subst f cst) b0 in
        Sub_FixM_l prf

    (* μr and νl rules. *)
    | (KFixN(o,f)  , _           ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let a = if eq_ordinal o' o then a else KFixN(o',f) in
            let p = subtype ctxt t (subst f a) b0 in
            Sub_FixM_r(p)
          with Not_found -> subtype_error "Subtyping clash (no rule apply)."
        end

    | (_           , KFixM(o,f)  ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let b = if eq_ordinal o' o then b else KFixM(o',f) in
            let p = subtype ctxt t a0 (subst f b) in
            Sub_FixN_l(p)
          with Not_found -> subtype_error "Subtyping clash (no rule apply)."
        end

    | (NuRec(ptr, a), _          )
        when Refinter.subset eq_ordinal ptr ctxt.positive_ordinals ->
       Sub_FixM_l(subtype ctxt t a b0)

    | (_           , MuRec(ptr, b))
        when Refinter.subset eq_ordinal ptr ctxt.positive_ordinals ->
       Sub_FixN_r(subtype ctxt t a0 b)

    (* Subtype clash. *)
    | (_           , _           ) ->
        subtype_error "Subtyping clash (no rule apply)."
  in (t, a0, b0, ind_ref, r)

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
    | TAbst(ao,f) ->
        let a = match ao with None -> new_uvar () | Some a -> a in
        let b = new_uvar () in
        let ptr = Refinter.create () in
        let c' = NuRec(ptr,KFunc(a,b)) in
        let p1 = subtype ctxt t c' c in
        let ctxt =  add_positives ctxt (Refinter.get ptr) in
        let wit = tcnst f a b in
        let p2 = type_check ctxt (subst f wit) b in
        Typ_Func_i(p1, p2)
    | TKAbs(f) ->
        let k = lambda_kind t c (binder_name f) in
        let p = type_check ctxt (subst f k) c in
        Typ_KAbs(p)
    | TOAbs(f) ->
        let k = lambda_ordinal t c (binder_name f) in
        let p = type_check ctxt (subst f k) c in
        Typ_OAbs(p)
    | TAppl(t,u) when is_neutral t && not (is_neutral u)->
        let a = new_uvar () in
        let ptr = Refinter.create () in
        let p2 = type_check ctxt t (MuRec(ptr,KFunc(a,c))) in
        let ctxt = add_positives ctxt (Refinter.get ptr) in
        let p1 = type_check ctxt u a in
        Typ_Func_e(p1, p2)
    | TAppl(t,u) ->
        let a = new_uvar () in
        let p1 = type_check ctxt u a in
        let p2 = type_check ctxt t (KFunc(a,c)) in
        Typ_Func_e(p1, p2)
    | TReco(fs) ->
        let ts = List.map (fun (l,_) -> (l, new_uvar ())) fs in
        let ptr = Refinter.create () in
        let c' = KProd(ts) in
        let c' = if is_normal t then NuRec(ptr,c') else c' in
        let p1 = subtype ctxt t c' c in
        let ctxt = add_positives ctxt (Refinter.get ptr) in
        let check (l,t) =
          let cl = List.assoc l ts in type_check ctxt t cl
        in
        let p2s = List.map check fs in
        Typ_Prod_i(p1, p2s)
    | TProj(t,l) ->
        let c' = KProd([(l,c)]) in
        let p = type_check ctxt t c' in
        Typ_Prod_e(p)
    | TCons(d,v) ->
        let a = new_uvar () in
        let c' = KDSum([(d,a)]) in
        let ptr = Refinter.create () in
        let c' = if is_normal t then NuRec(ptr,c') else c' in
        let p1 = subtype ctxt t c' c in
        let ctxt = add_positives ctxt (Refinter.get ptr) in
        let p2 = type_check ctxt v a in
        Typ_DSum_i(p1, p2)
    | TCase(t,l) ->
        let ts = List.map (fun (c,_) -> (c, new_uvar ())) l in
        let ptr = Refinter.create () in
        let p1 = type_check ctxt t (MuRec(ptr,(KDSum(ts)))) in
        let ctxt = add_positives ctxt (Refinter.get ptr) in
        let check (d,f) =
          let cc = List.assoc d ts in
          type_check ctxt f (KFunc(cc,c))
        in
        let p2s = List.map check l in
        Typ_DSum_e(p1, p2s)
    | TDefi(v) ->
        let p = subtype ctxt v.value v.ttype c in
        Typ_Defi(p)
    | TPrnt(_) ->
        let p = subtype ctxt t (KProd []) c in
        Typ_Prnt(p)

    | TFixY(n,f) ->
       let hyps = List.filter (function (_,Rec(f',_,_),_) -> f' == f | _ -> false)
         ctxt.induction_hyp in
       let a =
         match hyps with
         | (_,Rec(_,a,_),_) :: _ -> a
         | _ -> c
       in
       (* This is the subtyping that means that the program is typed *)
       let prf = subtype ctxt t a c in
       let (_, c0, os) = decompose Pos (KProd []) c in
       let pos = ctxt.positive_ordinals in
       Io.log_typ "searching induction hyp (1):\n  %a %a\n%!"
         (print_kind false) c print_positives ctxt;
       let rec fn = function
         | [] -> raise Not_found
         | (_,Sub _, _) :: hyps -> fn hyps
         | (_,Rec(_,_,a),[]) :: hyps -> fn hyps
         | (fnum,Rec(_,_,a),os') :: hyps ->
            try
              let ov = List.map (fun (i,_) -> (i,OUVar(ref None))) os' in
              let a = recompose a ov in
              Io.log_typ "searching induction hyp (1) with %d:\n%!" fnum;
              (* need full subtype to be sure to fail if sct fails *)
              let prf, _ = full_subtype ~ctxt ~term:t  a c in
              match ctxt.induction_hyp with
              | [] -> assert false
              | (cur,_,os0)::_   ->
                 Timed.(ctxt.delayed := (fun () ->
                   Io.log_typ "searching induction hyp (2):\n  %a => %a %a\n%!"
                     (print_kind false) a (print_kind false) c print_positives ctxt;
                   let m = find_indexes pos fnum cur ov os0 in
                   let call = (fnum, cur, m, true) in
                   (*Io.log "%d %a\n%!" afnum (print_call (Sct.arities ())) (fnum, cur, m);*)
                   ctxt.calls := call :: !(ctxt.calls)) :: !(ctxt.delayed));
                Typ_YH(fnum,prf)
            with Subtype_error _ -> fn hyps
       in
       (try fn hyps with Not_found ->
       if n = 0 then type_error t.pos "can not relate termination depth" else
       let fnum = new_function "Y" (List.map Latex.ordinal_to_printer os) in
       Io.log_typ "Adding induction hyp (1) %d:\n  %a => %a\n%!" fnum
         (print_kind false) c (print_kind false) c0;
       let pos = ctxt.positive_ordinals in
       let ctxt =
         begin match ctxt.induction_hyp with
         | [] -> ()
         | (cur,_,os0)::_   ->
            Timed.(ctxt.delayed := (fun () ->
              let m = find_indexes pos fnum cur os os0 in
              let call = (fnum, cur, m, false) in
              ctxt.calls := call :: !(ctxt.calls)) :: !(ctxt.delayed));
         end;
         { ctxt with induction_hyp = (fnum, Rec(f,a,c0), os)::ctxt.induction_hyp }
       in
       let p = type_check ctxt (subst f (in_pos t.pos (TFixY(n-1,f)))) c in
       Typ_Y(fnum,prf,p)) (* FIXME *)

    | TCnst(_,a,b) ->
        let p = subtype ctxt t a c in
        Typ_Cnst(p)
    | TTInt(_) -> assert false (* Cannot happen. *)
    | TVari(_) -> assert false (* Cannot happen. *)
    with Subtype_error msg ->
      Io.err "Typing failed: %a : %a\n%!" (print_term false) t (print_kind false) c;
      exit 1
  in (t, c, r)

and full_subtype : ?ctxt:subtype_ctxt -> ?term:term -> kind -> kind -> sub_prf * calls_graph =
  fun ?ctxt:ctxt0 ?term a b ->
    let t = from_opt term (generic_tcnst a b) in
    let ctxt =
      { (from_opt ctxt0 (empty_ctxt ())) with calls = ref []; delayed = ref [] }
    in
    let time = Timed.Time.save () in
    try
      let p = subtype ctxt t a b in
      List.iter (fun f -> f ()) !(ctxt.delayed);
      let calls = inline !(ctxt.calls) in
      let arities = Sct.arities () in
      if not (sct calls) then subtype_error "loop";
      if ctxt0 = None then reset_all ();
      (p, (arities, calls))
    with Subtype_error _ as e ->
      if ctxt0 = None then reset_all ();
      Timed.Time.rollback time;
      raise e
    | e ->
      Io.err "unexpected exception from subtype %s\n%!" (Printexc.to_string e);
      assert false

let subtype = full_subtype

let type_check : term -> kind option -> kind * typ_prf * calls_graph =
  fun t k ->
    let k = from_opt' k new_uvar in
    let ctxt = empty_ctxt () in
    let (prf, calls) =
      try
        let p = type_check ctxt t k in
        List.iter (fun f -> f ()) !(ctxt.delayed);
        let calls = inline !(ctxt.calls) in
        let arities = Sct.arities () in
        if not (sct calls) then subtype_error "loop";
        reset_all ();
        (p, (arities, calls))
      with e -> reset_all (); raise e
    in
    let fn v =
      match !(v.kuvar_state) with
      | Free   -> true
      | Sum  l -> set_kuvar false v (KDSum l); false
      | Prod l -> set_kuvar true  v (KProd l); false
    in
    let ul = List.filter fn (kuvar_list k) in
    let ol = ouvar_list k in
    let k = List.fold_left (fun acc v -> KKAll (bind_kuvar v acc)) k ul in
    let k = List.fold_left (fun acc v -> KOAll (bind_ouvar v acc)) k ol in
    (k, prf, calls)
