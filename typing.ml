open Bindlib
open Ast
open Print
open Proof_trace
open Sct
open Io

let debug = ref false

exception Type_error of pos * string
let type_error : pos -> string -> unit =
  fun p msg -> raise (Type_error(p,msg))

exception Subtype_error of string
let subtype_error : string -> 'a =
  fun msg -> raise (Subtype_error msg)

type subtype_ctxt =
  { induction_hyp     : (kind * kind * int * (int * ordinal) list) list
  ; calls             : calls ref
  ; positive_ordinals : (ordinal * ordinal list) list }

exception Found of cmp * int

let find_index a o =
  try
    let o = orepr o in
    List.iter (fun (i, o') -> if less_ordinal o o' then raise (Found(Less,i))
      else if leq_ordinal o o' then raise (Found(Leq,i))) a;
    (Unknown, -1)
  with Found(c,i) -> (c, i)

let find_indexes a b =
  let arity = List.length a in
  let indexes = Array.make arity 0 in
  let cmps = Array.make arity Unknown in
  List.iter (fun (i, o) -> let (c,j) = find_index b o in indexes.(i) <- j; cmps.(i) <- c) a;
  cmps, indexes

let try_inline ctxt num =
  let calls = ctxt.calls in
  let count, call = List.fold_left (
    fun (n,_ as acc) (i,j,c,a as call) ->
      if i = j then (2, None) else
      if i = num then (n + 1, Some call) else acc) (0,None) !calls in
  match count, call with
  | 1, Some(_,j,c,a) -> (* one use: do inlining *)
     calls := List.filter (fun (i,_,_,_) -> i <> num) !calls;
     calls := List.map (fun (i,k,c',a' as call) ->
       if k = num then
         let c'',a'' = compose c' a' c a in
         (i,j,c'',a'') else call) !calls
  | _ -> ()


let rec find_positive ctxt o =
  let o = orepr o in
  (*  Printf.eprintf "find positive %a\n%!" (print_ordinal false) o;*)
  try omax (List.assq o ctxt.positive_ordinals) with
  | Not_found ->
      match o with
  | OConv -> OConv
  | OUVar(o',ptr) -> OUVar(o, ref None)
  | OMaxi(l1) ->
     let rec fn = function
       | [] -> []
       | o::l ->
          let l = fn l in
          try find_positive ctxt o :: l with Not_found -> l
     in
     let l = fn l1 in
     (*     Printf.eprintf "%d %d \n%!" (List.length l1) (List.length l);*)
     if l = [] then raise Not_found else omax l
  | o -> raise Not_found

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
     io.log "KWith constraint on %s in %a\n%!" s (print_kind false) k;
     subtype_error ("Illegal use of \"with\" on variable "^s^".")

let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f) in
     if binder_name f = s then c else dot_proj t (subst f c) s
  | KWith(k,(s',a)) ->
     if s' = s then a else dot_proj t (with_clause k (s',a)) s
  | k ->
     raise Not_found

let rec elim_ord_quantifier t k =
  let l = ref [] in
  let rec fn k =
    match full_repr k with
    | KOExi(f) -> fn (subst f (OUVar(OConv, ref None)))
    | KOAll(f) ->
       let o = OLess(OConv,NotIn(t,f)) in
       l := (binder_name f, o)::!l;
       fn (subst f o)
    | KKAll(f) -> kkall (binder_name f) (fun x -> fn (subst f (KVari x)))
    | KKExi(f) -> kkexi (binder_name f) (fun x -> fn (subst f (KVari x)))
  (* fixme: more cases to search below mu and nu ? *)
    | _ -> lift_kind k
  in
  let r = unbox (fn k) in (!l, r)

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

let rec pos_kind k =
  match full_repr k with
  | KProd(fs) ->
     let rec fn = function
       | [] -> raise Not_found
       | (_,k)::l -> try pos_kind k with Not_found -> fn l
     in fn fs
  | _ -> raise Not_found

let rec neg_kind k =
  match full_repr k with
  | KFunc(a,b) ->
     (try pos_kind a with Not_found -> neg_kind k)
  | _ -> raise Not_found

let uwit_kind t f =
  (* FIXME: could use t *)
  neg_kind (subst f (dummy_pos (TTInt 0)))

let ewit_kind t f =
  (* FIXME: could use t *)
  pos_kind (subst f (dummy_pos (TTInt 0)))

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
    | KFixN(o,f) ->
       (* (match orepr o with OUVar _ -> raise Exit | _ -> ());*)
       fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)   -> fn (subst f (OTInt(-42)))
    | KUVar(u)   -> raise Exit
    | KDefi(d,a) -> Array.iter fn a
    | KWith(k,c) -> let (_,b) = c in fn k; fn b
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
    | t          -> ()
  in
  try
    fn k; false
  with
    Exit -> true


(* FIXME: end of the function which certainly miss cases *)

(****************************************************************************
 *                                 Lower kind                               *
****************************************************************************)

let lower_kind k1 k2 =
  (*positive integer are for eq_kind and alike *)
  let new_kint = let i = ref 0 in (fun () -> decr i; KTInt(!i)) in
  let new_oint = let i = ref 0 in (fun () -> decr i; OTInt(!i)) in
  let rec lower_kind first k01 k02 =
    (*if !debug then Printf.eprintf "    %a ≤ %a\n%!" (print_kind false) k1 (print_kind false) k2;*)
    match (full_repr k01, full_repr k02) with
    | (k1          , k2          ) when k1 == k2 -> true
    | (KVari(_)     , KVari(_)     ) -> assert false
    | (KFunc(a1,b1) , KFunc(a2,b2) ) -> lower_kind false a2 a1 && lower_kind false b1 b2
    | (KDSum(fsa)   , KDSum(fsb)   )
    | (KProd(fsa)   , KProd(fsb)   ) ->
       let cmp (k1,_) (k2,_) = compare k1 k2 in
       let f (la,a) (lb,b) = la = lb && lower_kind false a b in
       List.length fsa = List.length fsb &&
           List.for_all2 f (List.sort cmp fsa) (List.sort cmp fsb)
    | (KKAll(a)     , KKAll(b)     )
    | (KKExi(a)     , KKExi(b)     ) ->
       let i = new_kint () in
       lower_kind false (subst a i) (subst b i)
    | (KOAll(a)     , KOAll(b)     )
    | (KOExi(a)     , KOExi(b)     ) ->
       let i = new_oint () in
       lower_kind false (subst a i) (subst b i)
    | (KFixM(oa,fa) , KFixM(ob,fb) ) ->
       leq_ordinal oa ob && (fa == fb ||
         let i = new_kint () in
         lower_kind false (subst fa i) (subst fb i))
    | (KFixN(oa,fa) , KFixN(ob,fb) ) ->
       leq_ordinal ob oa &&
         (fa == fb ||
            let i = new_kint () in lower_kind false (subst fa i) (subst fb i))
    | (KDPrj(t1,s1) , KDPrj(t2,s2) ) -> s1 = s2 && eq_term t1 t2
    | (KWith(a1,(s1,b1))
      ,          KWith(a2,(s2,b2))) -> s1 = s2 && lower_kind false a1 a2 && lower_kind false b1 b2
    | (KUCst(t1,f1) , KUCst(t2,f2) )
    | (KECst(t1,f1) , KECst(t2,f2) ) ->
       let i = new_kint () in
       lower_kind false (subst f1 i) (subst f2 i) && eq_term t1 t2
    (* Handling of unification variables (immitation). *)
    | (KUVar(ua)    , KUVar(ub)    ) when ua == ub -> true
    | (KUVar ua as a,(KUVar _ as b)) ->
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) a (print_kind false) b;
        set_kuvar ua b; true
    | (KUVar ua as a, b           ) when true || first ->
        let k =
          match uvar_occur ua b with
          | Non -> k02
          | Pos -> KFixM(OConv,bind_uvar ua k02)
          | _   -> bot
        in
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) a (print_kind false) k;
        set_kuvar ua k; true
    | (a           ,(KUVar ub as b)) when true || first ->
        let k =
          match uvar_occur ub a with
          | Non -> k01
          | Pos -> KFixM(OConv,bind_uvar ub k01)
          | _   -> top
        in
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) b (print_kind false) k;
        set_kuvar ub k; true
    | (KTInt(ia)    , KTInt(ib)    ) -> ia = ib
    | (_            , _            ) -> false
  in
  Timed.pure_test (lower_kind true k1) k2

let cr = ref 0

let add_pos ctxt o o' =
  let o = orepr o and o' = orepr o' in
  if o = OConv then ctxt else
  let l = try List.assq o ctxt.positive_ordinals with Not_found -> [] in
  if List.memq o' l then ctxt else
    { ctxt with positive_ordinals = (o, o'::l) ::
        (List.filter (fun (o1,_) -> o1 != o) ctxt.positive_ordinals) }

type loop = int * (int * ordinal) list
type loops = loop list
exception Induction_hypothesis of loop

let check_rec : term -> subtype_ctxt -> kind -> kind ->
                  term * subtype_ctxt * (int * ordinal) list * int option =
  fun t ctxt a b ->
    (* FIXME: most comments in check_rec are probably obsolete ... *)
    (* the test (has_uvar a || has_uvar b) is important to
       - avoid occur chek for induction variable
       - to keep the invariant that no ordinal <> OConv occur in
       positive mus and negative nus *)
    (* has_leading_exists, is to keep maximum information about
       existential witnesses otherwise some dot projection fail *)
    try
      if has_uvar a || has_uvar b || has_leading_exists a then raise Exit;
      let (a', b', os) = decompose None Pos a b in
      (* Need induction for Nu left and Mu right, just to avoid loops *)
      (* Printf.eprintf "len(os') = %d\n%!" (List.length os');
         Printf.eprintf "(%a < %a)\n%!" (print_kind false) a' (print_kind false) b';*)
      let fnum = new_function (List.length os) in
      List.iter (fun (a0,b0,index,os0) ->
        if eq_kind a' a0 && eq_kind b0 b' then (
          raise (Induction_hypothesis(index,os)))) ctxt.induction_hyp;
      let t = if os = [] then t else generic_tcnst a b in
      let ctxt = { ctxt with induction_hyp = (a', b', fnum, os)::ctxt.induction_hyp } in
      (t, ctxt, os, Some fnum)
    with Exit ->
      (t, ctxt, [], None)

let delayed = ref []

let collect_pos ctxt w c c' =
  let (_,_,os) = decompose None Pos c c' in
  let rec fn ctxt o =
    match orepr o with
    | OLess(o',w') ->
      (*      Printf.eprintf "find pos ord %a %a\n%!" (print_ordinal true) o (print_term false) (snd w);*)
      let ctxt = fn ctxt o' in
      (match w,w' with
        (false, t), NotIn(t',_) when eq_term t' t -> add_pos ctxt o' o
      | (true, t), In(t',_) when eq_head_term t' t -> add_pos ctxt o' o
      | _ -> ctxt)
    | OMaxi(l1) ->
       List.fold_left fn ctxt l1
    | _ -> ctxt
  in
  List.fold_left fn ctxt (List.map snd os)

let rec subtype : subtype_ctxt -> term -> kind -> kind -> loops = fun ctxt t a b ->
  let rec subtype ctxt t a0 b0 : loops =
    let a = full_repr a0 in
    let b = full_repr b0 in
    if !debug then
      begin
        io.log "%a\n" (print_term false) t;
        io.log "  ∈ %a\n" (print_kind false) a;
        io.log "  ⊂ %a\n" (print_kind false) b;
        let p_aux ch (o,_) = print_ordinal false ch o in
        match ctxt.positive_ordinals with
        | [] -> io.log "\n%!"
        | l  -> io.log "  (0 < %a)\n\n%!" (print_list p_aux ", ") l
      end;
    (try
     if lower_kind a b then
       let _ = trace_subtyping t a0 b0 in
       trace_sub_pop NRefl;
       if !debug then
         begin
           io.log "%a ≤ %a" (print_kind false) a (print_kind false) b;
           io.log "(∋ %a)\n" (print_term false) t;
           let p_aux ch (o,_) = print_ordinal false ch o in
           match ctxt.positive_ordinals with
           | [] -> io.log "\n%!"
           | l  -> io.log "  (0 < %a)\n\n%!" (print_list p_aux ", ") l
         end;
       []
    else begin
      let (t, ctxt, os, index) = check_rec t ctxt a b in
      let loops = ref [] in
    let _ = trace_subtyping t a0 b0 in
    begin match (a,b) with
    (* Arrow type. *)
    | (KFunc(a1,b1), KFunc(a2,b2)) ->
        let f x = tappl dummy_position (box t) x in
        let bnd = unbox (bind (tvari_p dummy_position) "x" f) in
        let wit = tcnst bnd a2 b2 in
        if has_uvar b1 then begin
          loops := !loops @ subtype ctxt (dummy_pos (TAppl(t,wit))) b1 b2;
          loops := !loops @ subtype ctxt wit a2 a1;
        end else begin
          loops := !loops @ subtype ctxt wit a2 a1;
          loops := !loops @ subtype ctxt (dummy_pos (TAppl(t,wit))) b1 b2;
        end;
        trace_sub_pop NArrow

    (* Product type. *)
    | (KProd(fsa), KProd(fsb)) ->
        let check_field (l,b) =
          let a = try List.assoc l fsa with Not_found ->
            subtype_error ("Product fields clash: "^l) in
          loops := !loops @ subtype ctxt (dummy_pos (TProj(t,l))) a b
        in
        List.iter check_field fsb;
        trace_sub_pop NProd

    (* Sum type. *)
    | (KDSum([]), a)          -> trace_sub_pop NSum

    | (KDSum(csa), KDSum(csb)) ->
        let check_variant (c,a) =
          let t = unbox
            (tcase dummy_position (box t) [(c, idt)])
          in
          try
            let b = List.assoc c csb in
            loops := !loops @ subtype ctxt t a b
          with
            Not_found -> loops := !loops @ subtype ctxt t a (KDSum([]))
        in
        List.iter check_variant csa;
        trace_sub_pop NSum

    (* Dot projection. *)
    | (KDPrj(t0,s), _        ) ->
       let u = new_uvar () in
       type_check ctxt t0 u;
       loops := !loops @ subtype ctxt t (dot_proj t0 u s) b0;
       trace_sub_pop NProjLeft

    | (_        , KDPrj(t0,s)) ->
       let u = new_uvar () in
       type_check ctxt t0 u;
       loops := !loops @ subtype ctxt t a0 (dot_proj t0 u s);
       trace_sub_pop NProjRight

    (* KWith clause. *)
    | (KWith(a,e), _         ) ->
       loops := !loops @ subtype ctxt t (with_clause a e) b0;
       trace_sub_pop NWithLeft

    | (_        , KWith(b,e) ) ->
       loops := !loops @ subtype ctxt t a0 (with_clause b e);
       trace_sub_pop NWithRight

    (* Universal quantifier. *)
    | (_        , KKAll(f)   ) ->
       let b' = subst f (KUCst(t,f)) in
       loops := !loops @ subtype ctxt t a0 b';
       trace_sub_pop NAllRight

    | (KKAll(f)  , _         ) ->
       loops := !loops @ subtype ctxt t (subst f (new_uvar ())) b0;
       trace_sub_pop NAllLeft

    (* Existantial quantifier. *)
    | (KKExi(f)  , _         ) ->
       let a' = subst f (KECst(t,f)) in
       loops := !loops @ subtype ctxt t a' b0;
       trace_sub_pop NExistsLeft

    | (_        , KKExi(f)   ) ->
       loops := !loops @ subtype ctxt t a0 (subst f (new_uvar ()));
       trace_sub_pop NExistsRight

    (* Universal quantifier. *)
    | (_        , KOAll(f)   ) ->
       let b' = subst f (OLess(OConv,NotIn(t,f))) in
       loops := !loops @ subtype ctxt t a0 b';
       trace_sub_pop NAllRight

    | (KOAll(f)  , _         ) ->
       loops := !loops @ subtype ctxt t (subst f (OUVar(OConv, ref None))) b0;
       trace_sub_pop NAllLeft

    (* Existantial quantifier. *)
    | (KOExi(f)  , _         ) ->
       let a' = subst f (OLess(OConv,In(t,f))) in
       loops := !loops @ subtype ctxt t a' b0;
       trace_sub_pop NExistsLeft

    | (_        , KOExi(f)   ) ->
       loops := !loops @ subtype ctxt t a0 (subst f (OUVar(OConv, ref None)));
       trace_sub_pop NExistsRight

    (* μ and ν - least and greatest fixpoint. *)
    | (_          , KFixN(o,f)) ->
       let g = bind mk_free_ovari (binder_name f) (fun o ->
         bind_apply (Bindlib.box f) (box_apply (fun o -> KFixN(o,f)) o))
       in
       let o' = OLess (o,NotIn(t,unbox g)) in
       let ctxt = add_pos ctxt o o' in
       if !debug then io.log "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
       let cst = KFixN(o', f) in
       loops := !loops @ subtype ctxt t a0 (subst f cst);
       trace_sub_pop NNuRight

    | (KFixM(o,f)  , _        ) ->
       let g = bind mk_free_ovari (binder_name f) (fun o ->
         bind_apply (Bindlib.box f) (box_apply (fun o -> KFixM(o,f)) o))
       in
       let o' = OLess (o,In(t,unbox g)) in
       let ctxt = add_pos ctxt o o' in
       if !debug then io.log "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
       let cst = KFixM(o', f) in
       loops := !loops @ subtype ctxt t (subst f cst) b0;
       trace_sub_pop NMuLeft

    | (KFixN(o,f)  , _        ) ->
       (try
          let o' = find_positive ctxt o in
          let a = if o' = o then a else KFixN(o',f) in
          loops := !loops @ subtype ctxt t (subst f a) b0;
          trace_sub_pop NNuLeftInf
        with Not_found ->  subtype_error "Subtyping clash (no rule apply).")

    | (_          , KFixM(o,f)) ->
       (try
          let o' = find_positive ctxt o in
          let b = if o' = o then b else KFixM(o',f) in
          loops := !loops @ subtype ctxt t a0 (subst f b);
          trace_sub_pop NNuRightInf
        with Not_found ->  subtype_error "Subtyping clash (no rule apply).")

    (* Subtype clash. *)
    | (_, _) -> subtype_error "Subtyping clash (no rule apply)."
    end;
    match index with
      | None -> !loops
      | Some index ->
         List.iter (fun (index', os') ->
           (* index calls index' *)
           let a,b = find_indexes os' os in
           ctxt.calls := (index', index, a, b) :: !(ctxt.calls);
         ) !loops;
        [(index, os)]
    end;
    with Induction_hypothesis loop -> [loop] );
  in
  subtype ctxt t a b

and generic_subtype : kind -> kind -> unit = fun a b ->
  let calls = ref [] in
  let ctxt = { induction_hyp = []; positive_ordinals = []; calls } in
  let wit = generic_tcnst a b in
  let _ = subtype ctxt wit a b in
  if not (sct !calls)  then subtype_error "loop"

and wf_subtype : subtype_ctxt -> term -> kind -> kind -> unit = fun ctxt t a b ->
  let loops = subtype ctxt t a b in
  List.iter (fun (fnum, os) ->
    match ctxt.induction_hyp with
    | [] -> ()
    | (_,__,cur,os0)::_   ->
       let cmp, ind = find_indexes os os0 in
       let call = (fnum, cur, cmp, ind) in
       ctxt.calls := call :: !(ctxt.calls)) loops

and type_check : subtype_ctxt -> term -> kind -> unit = fun ctxt t c ->
  let c = repr c in
  if !debug then
    begin
      io.log "%a :\n" (print_term false) t;
      io.log "  %a\n" (print_kind false) c;
      let p_aux ch (o,_) = print_ordinal false ch o in
      match ctxt.positive_ordinals with
      | [] -> io.log "\n%!"
      | l  -> io.log "  (0 < %a)\n\n%!" (print_list p_aux ", ") l
    end;
  trace_typing t c;
  begin
    try match t.elt with
    | TCoer(t,a) ->
        wf_subtype ctxt t a c;
        type_check ctxt t a
    | TAbst(ao,f) ->
        let a = match ao with None -> new_uvar () | Some a -> a in
        let b = new_uvar () in
        let c' = KFunc(a,b) in
        wf_subtype ctxt t c' c;
        let ctxt = collect_pos ctxt (false,t) c c' in
        let wit = tcnst f a b in
        type_check ctxt (subst f wit) b
    | TKAbs(f) ->
       let k = lambda_kind t c (binder_name f) in
       type_check ctxt (subst f k) c
    | TOAbs(f) ->
       let k = lambda_ordinal t c (binder_name f) in
       type_check ctxt (subst f k) c
    | TAppl(t,u) ->
       let a = new_uvar () in
       type_check ctxt u a;
       type_check ctxt t (KFunc(a,c))
    | TReco(fs) ->
        let ts = List.map (fun (l,_) -> (l, new_uvar ())) fs in
        wf_subtype ctxt t (KProd(ts)) c;
        let check (l,t) =
          let cl = List.assoc l ts in
          type_check ctxt t cl
        in
        List.iter check fs
    | TProj(t,l) ->
        let c' = KProd([(l,c)]) in
        type_check ctxt t c'
    | TCons(d,v) ->
        let a = new_uvar () in
        let c' = KDSum([(d,a)]) in
        wf_subtype ctxt t c' c;
        type_check ctxt v a
    | TCase(t,l) ->
       let ts = List.map (fun (c,_) -> (c, new_uvar ())) l in
       let c' = KDSum(ts) in
       type_check ctxt t (KDSum(ts));
       let ctxt = collect_pos ctxt (true,t) c c' in
       let check (d,f) =
          let cc = List.assoc d ts in
          type_check ctxt f (KFunc(cc,c))
        in
        List.iter check l
    | TDefi(v) ->
        wf_subtype ctxt v.value v.ttype c
    | TPrnt(_) ->
       wf_subtype ctxt t (KProd []) c
    | TFixY(ko,f) ->
       (* what if KUVar ? -> error ? *)
       let c0 = match ko with
         | None -> c
         | Some k -> wf_subtype ctxt t k c; k
       in
       (* Elimination of KOAll in front of c0, keep ordinals to
          eliminate OAbs below Y *)
       let ords, c0 = elim_ord_quantifier t c0 in
       let (c,c0,os) =
         let (_, c, os) = decompose None Pos (KProd []) c0 in
         if os <> [] then c,c0,os
         else (
           (* Printf.eprintf "decompose\n%!"; *)
           let (_, c, os) = decompose (Some(YNotIn(t,c0))) Pos (KProd []) c0 in
           let c0 = recompose c os in
           (c,c0,os))
       in
       let fnum = new_function (List.length os) in
       if !debug then
         begin
           io.log "Adding induction hyp %d:\n" fnum;
           io.log "  %a => %a %a\n%!" (print_kind false) c0
             (print_kind false) c (print_term true) t;
         end;
       begin match ctxt.induction_hyp with
           [] -> ()
       | (_,_,cur,os0)::_   ->
            let cmp, ind = find_indexes os os0 in
            let call = (fnum, cur, cmp, ind) in
            ctxt.calls := call :: !(ctxt.calls);
       end;
       let ctxt = { ctxt with induction_hyp = (c, c, fnum, os)::ctxt.induction_hyp } in
       let wit = in_pos t.pos (TCstY(f,c)) in
       let t = subst f wit in
       (* Elimination of OAbs in front of t *)
       let rec fn t = match t.elt with
         | TOAbs f ->
            (try
              let o = List.assoc (binder_name f) ords in
              fn (subst f o)
            with Not_found -> t)
         | _       -> t
       in
       let t = fn t in
       type_check ctxt t c0

    | TCstY(_,a) ->
       if List.exists (fun (c',c'',fnum,os) ->
         if a == c'' && a == c' then
           match ctxt.induction_hyp with
               [] -> assert false
           | (_,_,cur,os0)::_   ->
              let ovars = List.map (fun (i,_) -> (i,OUVar(OConv,ref None))) os in
              let a = recompose a ovars in
              if !debug then
                begin
                  io.log "searching induction hyp (1) %d:\n" fnum;
                  io.log "  %a => %a\n%!" (print_kind false) a
                    (print_kind false) c
                end;
              wf_subtype ctxt t a c;
              delayed := (fun () ->
                if !debug then
                  begin
                    io.log "searching induction hyp (2) %d:\n" fnum;
                    io.log "  %a => %a\n%!" (print_kind false) a
                      (print_kind false) c
                  end;
                let cmp, ind = find_indexes ovars os0 in
                let call = (fnum, cur, cmp, ind) in
                ctxt.calls := call :: !(ctxt.calls)) :: !delayed;
              true
         else false) ctxt.induction_hyp then
         ()
       else
         assert false
    | TCnst(_,a,b) ->
       wf_subtype ctxt t a c
    | TTInt(_) -> assert false (* Cannot happen. *)
    | TVari(_) -> assert false (* Cannot happen. *)
    with
    | Subtype_error msg -> type_error t.pos msg
    | Stopped           -> type_error t.pos "subtype interrupted (loop?)"
  end;
  trace_typ_pop ()

let type_check t c =
  let calls = ref [] in
  let ctxt = { induction_hyp = []; positive_ordinals = []; calls } in
  type_check ctxt t c;
  List.iter (fun f -> f ()) !delayed;
  delayed := [];
  if not (sct !calls)  then subtype_error "loop"
