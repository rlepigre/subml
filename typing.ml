open Bindlib
open Ast
open Print
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
  { induction_hyp     : (int * induction_type * (int * ordinal) list) list
  ; calls             : pre_calls ref
  ; positive_ordinals : ordinal list }

and induction_type =
  | Sub of kind * kind
  | Rec of (term,term) binder * kind * kind

let find_indexes pos index index' a b =
  let (_, c) = Sct.arity index and (_, l) = Sct.arity index' in
  let m = Array.init l (fun _ -> Array.make c Unknown) in

  List.iter (fun (j,o') ->
    List.iter (fun (i,o) ->
      if less_ordinal pos o o' then m.(j).(i) <- Less
      else if leq_ordinal pos o o' then m.(j).(i) <- min m.(j).(i) Leq
    ) a) b;
  m

let rec find_positive ctxt o =
  let o = orepr o in
  (*  Printf.eprintf "find positive %a\n%!" (print_ordinal false) o;*)
  if List.exists (eq_ordinal o) ctxt.positive_ordinals then
    try List.hd (*omax*) (assoc_ordinal o !all_epsilons) with Not_found -> assert false
  else match o with
  | OConv -> OConv
  | OSucc o' -> o'
  | OUVar(p) ->
     let o' = OUVar(ref None) in
     set_ouvar p (OSucc o'); o'
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
       (match orepr o with OUVar _ -> raise Exit | _ -> ());
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

let uvar_list : kind -> uvar list = fun k ->
  let r = ref [] in
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
    | KUVar(u)   -> if not (List.memq u !r) then r := u :: !r
    | KDefi(d,a) -> Array.iter fn a
    | KWith(k,c) -> let (_,b) = c in fn k; fn b
    (* we ommit Dprj above because the kind in term are only
       indication for the type-checker and they have no real meaning *)
    | t          -> ()
  in
  fn k; !r

(* FIXME: end of the function which certainly miss cases *)

let cr = ref 0

let add_pos positives o =
  let o = orepr o in
  match o with
  | OConv | OSucc _ -> positives
  | _ ->
  if List.exists (eq_ordinal o) positives then positives else
    o :: positives

let add_positive ctxt o =
  { ctxt with positive_ordinals = add_pos ctxt.positive_ordinals o }

let add_positives ctxt gamma =
  let positive_ordinals =
    List.fold_left (fun positives o -> add_pos positives o)
      ctxt.positive_ordinals gamma
  in
  { ctxt with positive_ordinals }

exception Induction_hyp of int

let delayed = ref []

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
      (* Printf.eprintf "len(os') = %d\n%!" (List.length os');
         Printf.eprintf "(%a < %a)\n%!" (print_kind false) a' (print_kind false) b';*)
      let pos = ctxt.positive_ordinals in
      List.iter (function (_,Rec _,_) -> () | (index,Sub(a0,b0),os0) ->
        if Timed.pure_test (fun () -> eq_kind a' a0 && eq_kind b0 b') () then (
          match ctxt.induction_hyp with
          | (index',_,os')::_ ->
             Timed.(delayed := (fun () ->
               let m = find_indexes pos index index' os os' in
               ctxt.calls := (index, index', m, true) :: !(ctxt.calls)) :: !delayed);
             raise (Induction_hyp index)
          | _ -> assert false
        )) ctxt.induction_hyp;
      let fnum = new_function "S" (List.length os) in
      (match ctxt.induction_hyp with
      | (index',_,os')::_ ->
           Timed.(delayed := (fun () ->
             let m = find_indexes pos fnum index' os os' in
             ctxt.calls := (fnum, index', m, false) :: !(ctxt.calls)) :: !delayed);
      | _ -> ());
      let ctxt = { ctxt with induction_hyp = (fnum, Sub(a', b'), os)::ctxt.induction_hyp } in
      (Some fnum, None, ctxt)
    with Exit -> (None, None, ctxt)
       | Induction_hyp n -> (None, Some n, ctxt)

let fixpoint_depth = ref 3

let rec subtype : subtype_ctxt -> term -> kind -> kind -> sub_prf = fun ctxt t a0 b0 ->
  let a = full_repr a0 in
  let b = full_repr b0 in
  if !debug then
    begin
      io.log "%a\n" (print_term false) t;
      io.log "  ∈ %a\n" (print_kind false) a;
      io.log "  ⊂ %a\n" (print_kind false) b;
      let p_aux ch o = print_ordinal false ch o in
      match ctxt.positive_ordinals with
      | [] -> io.log "\n%!"
      | l  -> io.log "  (0 < %a)\n\n%!" (print_list p_aux ", ") l
    end;
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
       when (match !(ua.uvar_state) with Sum _ -> false | _ -> true) ->
       let l0 = match !(ua.uvar_state) with
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
       ua.uvar_state := Prod !l1;
       Sub_Lower

    | (KDSum(l)   , KUVar(ub)   )
       when (match !(ub.uvar_state) with Prod _ -> false | _ -> true) ->
       let l0 = match !(ub.uvar_state) with
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
       ub.uvar_state := Sum !l1;
       Sub_Lower

    (* Handling of unification variables (immitation). *)
    | (KUVar ua as a,(KUVar _ as b)) ->
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) a (print_kind false) b;
        set_kuvar ua b;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in r

    | (KUVar ua as a, b            ) ->
        let k =
          match uvar_occur ua b with
          | Non -> b0
          | Pos -> KFixM(OConv,bind_uvar ua b0)
          | _   -> bot
        in
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) a (print_kind false) k;
        set_kuvar ua k;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in r

    | (a           ,(KUVar ub as b))  ->
        let k =
          match uvar_occur ub a with
          | Non -> a0
          | Pos -> KFixM(OConv,bind_uvar ub a0)
          | _   -> top
        in
        if !debug then io.log "set %a <- %a\n\n%!" (print_kind false) b (print_kind false) k;
        set_kuvar ub k;
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
        (match a with KFixN(o',_) -> ignore (Timed.pure_test (leq_ordinal ctxt.positive_ordinals o) o') | _ -> ());
        let g = bind mk_free_ovari (binder_name f) (fun o ->
          bind_apply (Bindlib.box f) (box_apply (fun o -> KFixN(o,f)) o))
        in
        let o' = oless o (NotIn(t,unbox g)) in
        let ctxt = add_positive ctxt o in
        if !debug then
          io.log "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        let cst = KFixN(o', f) in
        let prf = subtype ctxt t a0 (subst f cst) in
        Sub_FixN_r prf

    | (KFixM(o,f)   , _           ) ->
        (match b with KFixM(o',_) -> ignore (Timed.pure_test (leq_ordinal ctxt.positive_ordinals o) o') | _ -> ());
        let g = bind mk_free_ovari (binder_name f) (fun o ->
          bind_apply (Bindlib.box f) (box_apply (fun o -> KFixM(o,f)) o))
        in
        let o' = oless o (In(t,unbox g)) in
        let ctxt = add_positive ctxt o in
        if !debug then
          io.log "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        let cst = KFixM(o', f) in
        let prf = subtype ctxt t (subst f cst) b0 in
        Sub_FixM_l prf

    (* μr and νl rules. *)
    | (KFixN(o,f)  , _           ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let a = if o' = o then a else KFixN(o',f) in
            let p = subtype ctxt t (subst f a) b0 in
            Sub_FixM_r(p)
          with Not_found -> subtype_error "Subtyping clash (no rule apply)."
        end

    | (_           , KFixM(o,f)  ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let b = if o' = o then b else KFixM(o',f) in
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
  if !debug then
    begin
      io.log "%a :\n" (print_term false) t;
      io.log "  %a\n" (print_kind false) c;
      let p_aux ch o = print_ordinal false ch o in
      match ctxt.positive_ordinals with
      | [] -> io.log "\n%!"
      | l  -> io.log "  (0 < %a)\n\n%!" (print_list p_aux ", ") l
    end;
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
    | TAppl(t,u) when is_neutral t ->
        let a = new_uvar () in
        let ptr = Refinter.create () in
        let p2 = type_check ctxt t (MuRec(ptr,KFunc(a,c))) in
        let ctxt = add_positives ctxt (Refinter.get ptr) in
        let p1 = type_check ctxt u a in
        Typ_Func_e(p1, p2)
    | TAppl(t,u) ->
        let a = new_uvar () in
        (*        let ctxt = add_positives ctxt (gamma_mu_term t) in*)
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
       if !debug then
         begin
           io.log "searching induction hyp (1):\n" ;
           io.log "  %a (%a > 0)\n%!"
             (print_kind false) c (fun ch -> List.iter (print_ordinal false ch)) pos;
         end;
       let rec fn = function
         | [] -> raise Not_found
         | (_,Sub _, _) :: hyps -> fn hyps
         | (fnum,Rec(_,_,a),os') :: hyps ->
            if List.length os = List.length os' then
              try
                let prf =
                  let time = Timed.Time.save () in
                  try (* If all these subtyping fails,
                         it is only a problem of terminaison *)
                    subtype ctxt t a c0
                  with _ ->
                    Timed.Time.rollback time;
                    raise Exit
                in
                match ctxt.induction_hyp with
                | [] -> assert false
                | (cur,_,os0)::_   ->
                   delayed := (fun () ->
                     if !debug then
                       begin
                         io.log "searching induction hyp (2) %d:\n" fnum;
                         io.log "  %a => %a (%a > 0)\n%!" (print_kind false) a
                           (print_kind false) c (fun ch -> List.iter (print_ordinal false ch)) pos
                       end;
                     let m = find_indexes pos fnum cur os os0 in
                     let call = (fnum, cur, m, true) in
                   (* Array.iter (fun x -> Format.eprintf "%a\n%!" print_cmp x) cmp; *)
                     ctxt.calls := call :: !(ctxt.calls)) :: !delayed;
                  Typ_YH(fnum,prf)
              with Exit -> fn hyps
            else
              fn hyps
       in
       (try fn hyps with Not_found ->
       if n = 0 then subtype_error "no ind found" else
       let fnum = new_function "Y" (List.length os) in
       if !debug then
         begin
           io.log "Adding induction hyp %d:\n" fnum;
           io.log "  %a => %a %a\n%!" (print_kind false) c
             (print_kind false) c0 (print_term true) t;
         end;
       let pos = ctxt.positive_ordinals in
       let ctxt =
         begin match ctxt.induction_hyp with
         | [] -> ()
         | (cur,_,os0)::_   ->
            delayed := (fun () ->
              let m = find_indexes pos fnum cur os os0 in
              let call = (fnum, cur, m, false) in
              ctxt.calls := call :: !(ctxt.calls)) :: !delayed;
         end;
         { ctxt with induction_hyp = (fnum, Rec(f,a,c0), os)::ctxt.induction_hyp }
       in
       let p = type_check ctxt (subst f t) c in
       Typ_Y(fnum,prf,p)) (* FIXME *)

    | TCnst(_,a,b) ->
        let p = subtype ctxt t a c in
        Typ_Cnst(p)
    | TTInt(_) -> assert false (* Cannot happen. *)
    | TVari(_) -> assert false (* Cannot happen. *)
    with Subtype_error msg ->
      Format.eprintf "Typing failed: %a : %a\n%!" (print_term false) t (print_kind false) c;
      exit 1
  in (t, c, r)

let subtype : term -> kind -> kind -> sub_prf * calls_graph
  = fun t a b ->
  let calls = ref [] in
  all_epsilons := [];
  let ctxt = { induction_hyp = []; positive_ordinals = []; calls } in
  try
    let p = subtype ctxt t a b in
    List.iter (fun f -> f ()) !delayed;
    delayed := [];
    let calls = inline !calls in
    let arities = Sct.arities () in
    if not (sct calls) then subtype_error "loop"; (p, (arities, calls))
  with e -> delayed := []; raise e

let generic_subtype : kind -> kind -> sub_prf * calls_graph = fun a b ->
  subtype (generic_tcnst a b) a b

let type_check : term -> kind -> typ_prf * calls_graph = fun t c ->
  let calls = ref [] in
  all_epsilons := [];
  let ctxt = { induction_hyp = [] ; positive_ordinals = [] ; calls } in
  try
    let p = type_check ctxt t c in
    List.iter (fun f -> f ()) !delayed;
    delayed := [];
    let calls = inline !calls in
    let arities = Sct.arities () in
    if not (sct calls) then subtype_error "loop"; (p, (arities, calls))
  with e -> delayed := []; raise e

let type_infer : term -> kind * typ_prf * calls_graph = fun t ->
  let k = new_uvar () in
  let (prf, calls) = type_check t k in
  (k, prf, calls)
