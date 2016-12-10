(** Main function for typing and subtyping *)

open Bindlib
open Ast
open Print
open Sct
open Position
open Compare
open Term
open Type
open Error

(** Raised in case of type error, not propagated because replaced by
    an error constructor in the proof *)
exception Type_error of string
let type_error : string -> 'a =
  fun msg -> raise (Type_error(msg))

(** Raised in case of subtyping error, not propagated because replaced by
    an error constructor in the proof *)
exception Subtype_error of string
let subtype_error : string -> 'a =
  fun msg ->
    Io.log_sub "CLASH: %s\n%!" msg;
    raise (Subtype_error msg)

(** Raised when the termination checkers fails, propagated *)
exception Loop_error of pos
let loop_error : pos -> 'a =
  fun p -> raise (Loop_error p)

type induction_node = int * (int * ordinal) list
type subtype_ctxt =
  { sub_induction_hyp : sub_induction list
  ; fix_induction_hyp : fix_induction list
  ; top_induction     : induction_node
  ; fun_table         : fun_table
  ; calls             : pre_calls ref
  ; delayed           : (unit -> unit) list ref
  ; positive_ordinals : ordinal list }

(** induction hypothesis for subtyping *)
and sub_induction =
      int                  (** the index of the induction hyp *)
    * int list             (** the positivity context *)
    * (int * int) list     (** the relation between ordinals *)
    * (ordinal, kind * kind) mbinder (** the two kinds *)

(** induction hypothesis for typing recursive programs *)
and fix_induction =
      (term',term) binder     (* the argument of the fixpoint combinator *)
    * kind                    (* the initial type, if no initial ordinal params *)
              (* the induction hypothesis collected so far for this fixpoint *)
    * (int                    (* reference of the inductive hyp *)
       * int list             (** the positivity context *)
       * (int * int) list     (** the relation between ordinals *)
       * (ordinal, kind * kind) mbinder) (** the kind, ignore the first *)
      list ref
    * (subtype_ctxt * kind * (int * typ_prf) ref) list ref (* proofs yet to be done *)
      (* The use of references here is to do a breadth-first search for
         inductive proof. Depth first here is bad, using too large depth *)

(** the initial empty context *)
let empty_ctxt () =
  { sub_induction_hyp = []
  ; fix_induction_hyp = []
  ; top_induction = (-1, [])
  ; fun_table = init_fun_table ()
  ; calls = ref []
  ; delayed = ref []
  ; positive_ordinals = [] }



(****************************************************************************
 *                               SCT functions                              *
 ****************************************************************************)

let consecutive =
  let rec fn n = function
    | [] -> true
    | (p,_)::l when n = p -> fn (n+1) l
    | _ -> false
  in fn 0

let find_indexes ftbl pos index index' a b =
  Io.log_mat "build matrix for %d %d\n" index index';
  let c = Sct.arity index ftbl and l = Sct.arity index' ftbl in
  let m = Array.init l (fun _ -> Array.make c Unknown) in
  List.iteri (fun j (j',o') ->
    assert(j=j');
    List.iteri (fun i (i',o) ->
      assert(i=i');
      Io.log_mat "  compare %d %a <=? %d %a => %!" i (print_ordinal false) o
        j (print_ordinal false) o';
      let r =
        if less_ordinal pos o o' then Less
        else if leq_ordinal pos o o' then Leq
        else Unknown
      in
      Io.log_mat "%a\n%!" print_cmp r;
      assert(j < l);
      assert(i < c);
      m.(j).(i) <- r
    ) a) b;
  m

let add_call ctxt fnum os is_induction_hyp =
  let pos = ctxt.positive_ordinals in
  let calls = ctxt.calls in
  let cur, os0 = ctxt.top_induction in
  assert(consecutive os);
  assert(consecutive os0);
  let ftbl = ctxt.fun_table in
  Io.log_mat "adding call %d(%d=%d) -> %d(%d=%d)\n%!"
    cur (Sct.arity cur ftbl) (List.length os0) fnum (Sct.arity fnum ftbl) (List.length os);
  Timed.(ctxt.delayed := (fun () ->
    let m = find_indexes ftbl pos fnum cur os os0 in
    let call = (fnum, cur, m, is_induction_hyp) in
    calls := call :: !calls) :: !(ctxt.delayed))

let find_positive ctxt o =
  let rec gn i o =
    if i <= 0 then
      List.exists (strict_eq_ordinal o) ctxt.positive_ordinals
    else
      List.exists (function
      | OLess(o',_) as o0 when strict_eq_ordinal o o' -> gn (i-1) o0
      | _ -> raise Not_found) ctxt.positive_ordinals
  in
  let rec fn i o = match orepr o with
    | OUVar({ uvar_state = (_,Some f)},os) ->
       let b = msubst f os in
       fn (i+1) b
    | OConv -> true
    | OSucc o -> if i >= 0 then true else fn (i-1) o
    | OLess(_) as o -> gn i o
    | OUVar _ -> true
    | OVari _ -> assert false
  in
  (*  Io.log "find positive %a\n%!" (print_ordinal false) o;*)
  match orepr o with
  | OConv -> OConv
  | OSucc o' -> o'
  | o ->
     if not (fn 0 o) then raise Not_found;
     new_ouvar ~upper:(constant_mbind 0 o) ()

let is_positive ctxt o =
  match orepr o with
  | OConv | OSucc _ -> true
  | o -> List.exists (fun o' -> leq_ordinal ctxt.positive_ordinals o' o) ctxt.positive_ordinals

let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in (* NOTE: used only for close term *)
     if binder_name f = s then c else dot_proj t (subst f c) s
  | k ->
     raise Not_found

let lambda_kind t k s = match full_repr k with
  | KKAll(f) when binder_name f = s ->
     let c = KUCst(t,f,true) in (* NOTE: used only for close term *)
     c, (subst f c)
  | _ -> type_error ("type lambda mismatch for "^s)

let lambda_ordinal t k s =
  match full_repr k with
  | KOAll(f) when binder_name f = s ->
     let c = OLess(OConv, NotIn(t,f)) in
     c, (subst f c)
  | _ -> Io.err "%a\n%!" (print_kind false) k; type_error ("ordinal lambda mismatch for "^s)

(* These three functions are only used for heuristics *)
let has_leading_ord_quantifier : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(a,b) -> fn b
    | KProd(ls)
    | KDSum(ls)  -> List.exists (fun (l,a) -> fn a) ls
    | KOAll(f)
    | KOExi(f)   -> true
    | KKAll(f)
    | KKExi(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f (KProd []))
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | _ -> false
  in
  fn k

(* These three functions are only used for heuristics *)
let has_leading_exists : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(a,b) -> false
    | KProd(ls)
    | KDSum(ls)  -> List.exists (fun (l,a) -> fn a) ls
    | KKExi(f)   -> true
    | KOExi(f)   -> true
    | KOAll(f)   -> fn (subst f OConv)
    | KKAll(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f (KProd []))
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | _ -> false
  in
  fn k

let has_leading_forall : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(a,b) -> false
    | KProd(ls)
    | KDSum(ls)  -> List.exists (fun (l,a) -> fn a) ls
    | KKAll(f)   -> true
    | KOAll(f)   -> true
    | KOExi(f)   -> fn (subst f OConv)
    | KKExi(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f (KProd []))
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
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
    | KFixM(o,f) -> fn (subst f (KProd []))
    | KFixN(o,f) -> fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)   -> fn (subst f OConv)
    | KUVar(u,_) -> raise Exit
    | KDefi(d,o,a) -> Array.iter fn a
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | KVari _    -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd []))
  in
  try
    fn k; false
  with
    Exit -> true

(* FIXME: what to do with duplicates, probably OK *)
let kuvar_list : kind -> (kuvar * ordinal array) list = fun k ->
  let r = ref [] in
  let adone = ref [] in
  let rec fn k =
    let k = repr k in
    if List.memq k !adone then () else (
    adone := k::!adone;
    match k with
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f OConv)
    | KUVar(u,os)  ->
       begin
         match !(u.uvar_state) with
         | Free -> ()
         | Sum l | Prod l ->
            List.iter (fun (c,f) -> fn (msubst f (Array.make (mbinder_arity f) OConv))) l
       end;
       if not (List.exists (fun (u',_) -> eq_uvar u u') !r) then
         r := (u,os) :: !r
    | KDefi(d,_,a) -> Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd [])))
  in
  fn k; !r

let ouvar_list : kind -> ouvar list = fun k ->
  let r = ref [] in
  let adone = ref [] in
  let rec fn k =
    let k = repr k in
    if List.memq k !adone then () else (
    adone := k::!adone;
    match k with
    | KUVar(_,_)   -> () (* ignore ordinals, will be constant *)
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f (KProd []))
    | KFixM(o,f)
    | KFixN(o,f)   -> gn o; fn (subst f (KProd []))
    | KOAll(f)
    | KOExi(f)     -> fn (subst f OConv)
    | KDefi(d,o,a) -> Array.iter gn o;  Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd [])))
  and gn o =
    match orepr o with
    | OSucc(o)   -> gn o
    | OUVar(v,_) -> if not (List.exists (eq_uvar v) !r) then r := v :: !r
    | OConv      -> ()
    | OLess _    -> ()
    | OVari _    -> ()
  in
  fn k; !r

(* FIXME: end of the function which certainly miss cases *)

let print_positives ff ctxt =
  let p_aux = print_ordinal false in
  match ctxt.positive_ordinals with
      | [] -> ()
      | l -> Io.log "  (%a)\n\n%!" (print_list p_aux ", ") l

let rec add_pos positives o =
  let o = orepr o in
  match o with
  | OConv | OSucc _ -> positives
  | _ ->
    if List.exists (strict_eq_ordinal o) positives then positives else o :: positives

let add_positive ctxt o =
  { ctxt with positive_ordinals = add_pos ctxt.positive_ordinals o }

let add_positives ctxt gamma =
  let positive_ordinals =
    List.fold_left add_pos ctxt.positive_ordinals gamma
  in
  { ctxt with positive_ordinals }

exception Induction_hyp of int

type induction =
  | UseInduction of int
  | NewInduction of (int * kind * kind) option

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
       ignore (leq_ordinal ctxt.positive_ordinals o o')
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
      let pos = ctxt.positive_ordinals in
      let (ipos, rel, both, os) = generalise pos a b in
      let (os0,tpos,k1,k2) = recompose ipos rel both false in
      let fnum = new_function ctxt.fun_table "S" (List.map Latex.ordinal_to_printer os0) in
      add_call ctxt fnum os false;
      let ctxt = { ctxt with
        sub_induction_hyp = (fnum, ipos, rel, both)::ctxt.sub_induction_hyp;
        positive_ordinals = tpos;
        top_induction = (fnum, os0)
      } in
      List.iter (function (index,pos0,rel0,both0) ->
        (* hypothesis apply if same type up to the parameter and same positive ordinals.
           An inclusion beween p' and p0 should be enough, but this seems complete that
           way *)
(*        Io.log_sub "PRE %d %d\n%a = %a\n\n%!" (mbinder_arity both0) (mbinder_arity both)
          (print_kind false) k1  (print_kind false) k2;*)
        let (ov,pos',a',b') = recompose pos0 rel0 both0 true in
        Io.log_sub "TESTING %a = %a\n%a = %a\n\n%!"
          (print_kind false) k1  (print_kind false) a'
          (print_kind false) k2  (print_kind false) b';
        if leq_kind tpos k1 a' && leq_kind tpos b' k2 && (Io.log_sub "EQ OK\n%!"; true) &&
           List.for_all (fun o1 ->
               List.exists (eq_ordinal tpos o1) tpos) pos'
        then (
          Io.log_sub "By induction\n\n%!";
          add_call ctxt index ov true;
          raise (Induction_hyp index))
      ) (List.tl ctxt.sub_induction_hyp);
      Io.log_sub "NEW %a < %a\n%!" (print_kind false) k1 (print_kind false) k2;
      (NewInduction (Some (fnum, k1, k2)), ctxt)
    with Exit            -> (NewInduction None, ctxt)
       | Induction_hyp n -> (UseInduction n, ctxt)

let fixpoint_depth = ref 1

let rec subtype : subtype_ctxt -> term -> kind -> kind -> sub_prf = fun ctxt t a0 b0 ->
  Io.log_sub "%a\n  ∈ %a\n  ⊂ %a\n  %a\n\n%!"
    (print_term false) t (print_kind false) a0 (print_kind false) b0
    print_positives ctxt;
  let a = full_repr a0 in
  let b = full_repr b0 in
  if leq_kind ctxt.positive_ordinals a b (*strict_eq_kind a b*) then
    (t, a0, b0, None, Sub_Lower)
  else (
    try
    let ind_ref, r = match (a,b) with
    | (KMRec(ptr,a), _           ) ->
       None, Sub_And_l(subtype ctxt t a b0)

    | (_           , KNRec(ptr,b))->
       None, Sub_Or_r(subtype ctxt t a0 b)

    | (KNRec(ptr,a), KUVar _     )
        when Subset.test (eq_ordinal ctxt.positive_ordinals) ptr ctxt.positive_ordinals ->
       None, Sub_Or_l(subtype ctxt t a b0)

    | (KUVar _     , KMRec(ptr,b))
        when Subset.test (eq_ordinal ctxt.positive_ordinals) ptr ctxt.positive_ordinals ->
       None, Sub_And_r(subtype ctxt t a0 b)

    (* unification. (sum and product special) *)
    | (KUVar(ua,os), KProd(l))
       when (match !(ua.uvar_state) with Sum _ -> false | _ -> true) ->
       let l0 = match !(ua.uvar_state) with
           Free -> []
         | Prod l -> l
         | Sum _ -> assert false
       in
       let l1 = ref l0 in
       let res = ref [] in
       List.iter (fun (s,k) ->
         let t' = dummy_pos (TProj(t,s)) in
         try
           let prf = subtype ctxt t' (msubst (List.assoc s l0) os) k  in
           res := (s,prf) :: !res
         with
           Not_found ->
             let f = bind_ordinals os k in
             l1 := (s,f)::!l1;
             let prf = subtype ctxt t' (msubst f os) k  in
             res := (s,prf) :: !res) l;
       Timed.(ua.uvar_state := Prod !l1);
       None, Sub_Prod(!res)

    | (KDSum(l)   , KUVar(ub,os))
       when (match !(ub.uvar_state) with Prod _ -> false | _ -> true) ->
       let l0 = match !(ub.uvar_state) with
           Free -> []
         | Sum l -> l
         | Prod _ -> assert false
       in
       let l1 = ref l0 in
       let res = ref [] in
       List.iter (fun (s,k) ->
         let t' = unbox (tcase dummy_position (box t) [(s, idt)] None) in
         try
           let prf = subtype ctxt t' k (msubst (List.assoc s l0) os)  in
           res := (s,prf) :: !res
         with
           Not_found ->
             let f = bind_ordinals os k in
             l1 := (s,f)::!l1;
             let prf = subtype ctxt t' k (msubst f os) in
             res := (s,prf) :: !res) l;
       Timed.(ub.uvar_state := Sum !l1);
       None, Sub_DSum(!res)

    (* Handling of unification variables, same variable different
       parameters: keep the common one only. *)
    | (KUVar(ua,osa),KUVar(ub,osb)) when eq_uvar ua ub ->
       let osal = Array.to_list osa in
       let osbl = Array.to_list osb in
       let (_,os) = List.fold_left2 (fun (i,acc) o1 o2 ->
         if eq_ordinal ctxt.positive_ordinals o1 o2 then
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
         safe_set_kuvar Neg ua f osa);
       let (_,_,_,_,r) = subtype ctxt t a0 b0 in None, r

    (* Handling of unification variables (immitation). *)
    | ((KUVar(ua,osa) as a),(KUVar(ub,osb) as b)) ->
       begin (* make the correct choice, depending if Sum or Prod *)
          match !(ua.uvar_state), !(ub.uvar_state) with
          | _, Sum _ -> safe_set_kuvar Neg ua (bind_ordinals osa b) osa
          | Prod _, _ -> safe_set_kuvar Pos ub (bind_ordinals osb a) osb
          | _ ->
               let osal = Array.to_list osa in
               let osbl = Array.to_list osb in
               let os = List.fold_left (fun acc o ->
                 if List.exists (strict_eq_ordinal o) acc then acc
                 else
                   if   (List.exists (strict_eq_ordinal o) osal &&
                         List.exists (strict_eq_ordinal o) osbl)
                     || (List.exists (strict_eq_ordinal o) osal && not (kuvar_ord_occur ub o))
                     || (List.exists (strict_eq_ordinal o) osbl && not (kuvar_ord_occur ua o))
                   then o::acc
                   else acc) [] (osal @ osbl)
               in
               let os = Array.of_list os in
               let new_len = Array.length os in
               let state =
                 match !(ua.uvar_state), !(ub.uvar_state) with
                 | Free, Free -> Free
                 | Sum l, _ ->
                    Sum (List.map (fun (s,f) ->
                      (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                        bind_fn new_len os x (msubst f osa))))) l)
                 | _, Prod l ->
                    Prod (List.map (fun (s,f) ->
                      (s, unbox (mbind mk_free_ovari (Array.make new_len "α") (fun x ->
                        bind_fn new_len os x (msubst f osb))))) l)
                 | _ -> assert false
               in
               let u = new_kuvara ~state new_len in
               let k = KUVar(u,os) in
               (* NOTE: the call to  bind_fn above may (very rarely) instanciate
                  ua or ub, so we added a test to avoid an assert false  *)
               if !(ua.uvar_val) = None then (
                 Timed.(ua.uvar_state := Free);
                 safe_set_kuvar Neg ua (bind_ordinals osa k) osa);
               if !(ub.uvar_val) = None then (
                 Timed.(ub.uvar_state := Free);
                 safe_set_kuvar Pos ub (bind_ordinals osb k) osb);
        end;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in None, r

    | (KUVar(ua,os), b            ) ->
        safe_set_kuvar Neg ua (bind_ordinals os b0) os;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in None, r

    | (a           ,(KUVar(ub,os)))  ->
        safe_set_kuvar Pos ub (bind_ordinals os a0) os;
        let (_,_,_,_,r) = subtype ctxt t a0 b0 in None, r

    | _ ->

  let (ind_res, ctxt) = check_rec t ctxt a b in
  match ind_res with
  | UseInduction n -> (None, Sub_Ind n)
  | NewInduction ind_ref ->
  let (ind_ref,t,a,b,a0,b0) = match ind_ref with
    | None -> (None,t,a,b,a0,b0)
    | Some(n,a,b) ->
       let a = full_repr a and b = full_repr b in
       let t = unbox (generic_tcnst (box a) (box b)) in
       Some n, t, a, b, a, b
  in
  let r =
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
             let o' = opred o (NotIn(t,unbox g)) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        Io.log_sub "creating %a < %a\n%!" (print_ordinal true) o' (print_ordinal true) o;
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
             let o' = opred o (In(t,unbox g)) in
             let ctxt = add_positive ctxt o in
             o', ctxt
        in
        Io.log_sub "creating %a < %a\n%!" (print_ordinal false) o' (print_ordinal false) o;
        Io.log_sub "creating %a < %a\n%!" (print_ordinal true) o' (print_ordinal true) o;
        let cst = KFixM(o', f) in
        let prf = subtype ctxt t (subst f cst) b0 in
        Sub_FixM_l prf

    (* μr and νl rules. *)
    | (KFixN(o,f)  , _           ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let a = if o' = OConv then a else KFixN(o',f) in
            let p = subtype ctxt t (subst f a) b0 in
            if not (is_positive ctxt o) then raise Not_found;
            Sub_FixM_r(p)
          with Not_found -> subtype_error "Subtyping clash (no rule apply)."
        end

    | (_           , KFixM(o,f)  ) ->
        begin
          try
            let o' = find_positive ctxt o in
            let b = if o' = OConv then b else KFixM(o',f) in
            let p = subtype ctxt t a0 (subst f b) in
            if not (is_positive ctxt o) then raise Not_found;
            Sub_FixN_l(p)
          with Not_found -> subtype_error "Subtyping clash (no rule apply)."
        end

    (* Universal quantification over kinds. *)
    | (_           , KKAll(f)    ) ->
        let p = subtype ctxt t a0 (subst f (KUCst(t,f,true))) in
        Sub_KAll_r(p)

    | (KKAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (new_kuvar ())) b0 in
        Sub_KAll_l(p)

    (* Existantial quantification over kinds. *)
    | (KKExi(f)    , _           ) ->
        let p = subtype ctxt t (subst f (KECst(t,f,true))) b0 in
        Sub_KExi_l(p)

    | (_           , KKExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (new_kuvar ())) in
        Sub_KExi_r(p)

    (* Universal quantification over ordinals. *)
    | (_           , KOAll(f)    ) ->
        let p = subtype ctxt t a0 (subst f (OLess(OConv, NotIn(t,f)))) in
        Sub_OAll_r(p)

    | (KOAll(f)    , _           ) ->
        let p = subtype ctxt t (subst f (new_ouvar ())) b0 in
        Sub_OAll_l(p)

    (* Existantial quantification over ordinals. *)
    | (KOExi(f)    , _           ) ->
        let p = subtype ctxt t (subst f (OLess(OConv, In(t,f)))) b0 in
        Sub_OExi_l(p)

    | (_           , KOExi(f)    ) ->
        let p = subtype ctxt t a0 (subst f (new_ouvar ())) in
        Sub_OExi_r(p)

    | (KNRec(ptr, a), _          )
        when Subset.test (eq_ordinal ctxt.positive_ordinals) ptr ctxt.positive_ordinals ->
       Sub_And_l(subtype ctxt t a b0)

    | (_           , KMRec(ptr, b))
        when Subset.test (eq_ordinal ctxt.positive_ordinals) ptr ctxt.positive_ordinals ->
       Sub_Or_r(subtype ctxt t a0 b)

    (* Subtype clash. *)
    | (_           , _           ) ->
       subtype_error "Subtyping clash (no rule apply)."
  in (ind_ref, r)
  in (t, a0, b0, ind_ref, r)
  with Subtype_error e -> (t, a0, b0, None, Sub_Error e)
       | Occur_check -> (t, a0, b0, None, Sub_Error "Occur_check"))



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
        let a = match ao with None -> new_kuvar () | Some a -> a in
        let b = new_kuvar () in
        let ptr = Subset.create ctxt.positive_ordinals in
        let c' = KNRec(ptr,KFunc(a,b)) in
        let p1 = subtype ctxt t c' c in
        let ctxt = add_positives ctxt (Subset.get ptr) in
        let wit = unbox (tcnst f (box a) (box b)) in
        let p2 = type_check ctxt (subst f wit.elt) b in
        Typ_Func_i(p1, p2)
    | TKAbs(f) ->
        let k, b = lambda_kind t c (binder_name f) in
        let p = type_check ctxt (subst f k) b in
        Typ_KAbs(p)
    | TOAbs(f) ->
        let k, b = lambda_ordinal t c (binder_name f) in
        let p = type_check ctxt (subst f k) b in
        Typ_OAbs(p)
    | TAppl(t,u) when is_neutral t && not (is_neutral u)->
        let a = new_kuvar () in
        let ptr = Subset.create ctxt.positive_ordinals in
        let p2 = type_check ctxt t (KMRec(ptr,KFunc(a,c))) in
        let ctxt = add_positives ctxt (Subset.get ptr) in
        let p1 = type_check ctxt u a in
        Typ_Func_e(p1, p2)
    | TAppl(t,u) ->
        let a = new_kuvar () in
        let p1 = type_check ctxt u a in
        let p2 = type_check ctxt t (KFunc(a,c)) in
        Typ_Func_e(p1, p2)
    | TReco(fs) ->
        let ts = List.map (fun (l,_) -> (l, new_kuvar ())) fs in
        let c' = KProd(ts) in
        let ptr = Subset.create ctxt.positive_ordinals in
        let c' =
          if is_normal t then KNRec(ptr,c') else c'
        in
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
        let c' = new_kuvar ~state:(Sum [(d,constant_mbind 0 a)]) () in
        let ptr = Subset.create ctxt.positive_ordinals in
        let c' =
          if is_normal t then
            KNRec(ptr,c')
          else c'
        in
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
             new_kuvar ~state:(Sum ts) ()
        in
        let ptr = Subset.create ctxt.positive_ordinals in
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
          | Some f, KUVar({ uvar_state = { contents = Sum ts }}, os)  ->
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
    | TCnst(_,a,b,_) ->
        let p = subtype ctxt t a c in
        Typ_Cnst(p)
    | TVari(_) -> assert false
    with Subtype_error msg
    | Type_error msg -> Typ_Error msg
    | Occur_check    -> Typ_Error "occur_check"
  in (t, c, r)

and subsumption acc = function
  | [] -> List.rev acc
  | (ctxt,t,c,ptr,subsumed as head)::tail ->
     let forward = ref false in
     let rec gn acc' = function
       | [] -> subsumption (head::List.rev acc') tail
       | (ctxt',t',c',ptr',subsumed' as head')::tail' ->
          try
            if not (List.for_all (fun o1 ->
              List.exists (strict_eq_ordinal o1) ctxt.positive_ordinals)
                      ctxt'.positive_ordinals)
            then raise Exit;
            let prf = subtype ctxt t c' c in
            check_sub_proof prf;
            assert (not !forward);
            subsumed' := ctxt :: !subsumed @ !subsumed';
            subsumption acc tail
          with Exit | Subtype_error _ | Error.Error _ ->
            try
              if not (List.for_all (fun o1 ->
                List.exists (strict_eq_ordinal o1) ctxt'.positive_ordinals)
                        ctxt.positive_ordinals)
              then raise Exit;
              let prf = subtype ctxt' t' c c' in
              check_sub_proof prf;
              forward := true;
              subsumed := ctxt' :: !subsumed' @ !subsumed;
              gn acc' tail'
            with Exit | Subtype_error _ | Error.Error _ ->
              gn (head'::acc') tail'
     in gn [] acc

and breadth_first proof_ptr hyps_ptr f remains do_subsume depth =
      if depth = 0 && !remains <> [] then
         (* the fixpoint was unrolled as much as allowed, and
            no applicable induction hyp was found. *)
        type_error "can not relate termination depth"
      else
        (* otherwise we unroll once more, and type-check *)
        let l = List.map (fun (ctxt,c,ptr) ->
          let t =  subst f (TFixY(do_subsume,depth-1,f)) in
          ctxt,t,c,ptr,ref []) !remains
        in
        let l = if do_subsume then subsumption [] l else l in
        let l = List.map (fun (ctxt,t,c,ptr,subsumed) ->
          let (pos, rel, both, os) = generalise ctxt.positive_ordinals (KProd []) c in
          let (os0, tpos, _, c0) = recompose pos rel both false in
          let fnum = new_function ctxt.fun_table "Y" (List.map Latex.ordinal_to_printer os0) in
          Io.log_typ "Adding induction hyp (1) %d:\n  %a => %a\n%!" fnum
            (print_kind false) c (print_kind false) c0;
          List.iter (fun ctxt -> add_call ctxt fnum os false) (ctxt::!subsumed);
          if os <> [] then hyps_ptr := (fnum, pos, rel, both) :: !hyps_ptr;
          let ctxt = { ctxt with top_induction = (fnum, os0); positive_ordinals = tpos} in
          Some (ctxt,t,c0,fnum,ptr)) l
        in
        let l = List.fold_left (fun acc -> function
          | None -> acc
          | Some x -> x::acc) [] l
        in
        remains := [];

        List.iter (fun (ctxt,t,c,fnum,ptr) -> ptr := (-1, type_check ctxt t c)) l;
        if !remains = [] then
          Typ_TFix(proof_ptr)
        else
          breadth_first proof_ptr hyps_ptr f remains do_subsume (depth-1)

and search_induction depth ctxt t a c0 hyps =
  (* fn search for an applicable inductive hypothesis *)
  Io.log_typ "searching induction hyp (1):\n  %a %a\n%!"
    (print_kind false) c0 print_positives ctxt;
  (* NOTE: HEURISTIC THAT AVOID SOME FAILURE, BY FORCING SOME UNIFICATIONS,
     can we do better ? *)
  let _ =
    (* We protect the context to avoid adding calls to the sct *)
    let ctxt = { ctxt with
      calls = ref [];
      delayed = ref[];
      fun_table = copy_table ctxt.fun_table} in
    try Timed.pure_test (fun () -> let prf = subtype ctxt t a c0 in check_sub_proof prf; true) ()
      with Subtype_error _ | Error _ -> true
  in

  let rec fn = function
    | _ when depth > 0 ->
       (* If the depth is not zero, only apply the above heuristic, but
          do not search really the induction hypothesis *)
       raise Not_found
    | [] -> Io.log_typ "no induction hyp found\n%!"; raise Not_found
    | (fnum, pos', rel', both) :: hyps ->
       try
         let (ov, pos, _, a) = recompose pos' rel' both true in
         Io.log_typ "searching induction hyp (2) with %d %a ~ %a <- %a:\n%!"
           fnum (print_kind false) a (print_kind false) c0
           print_positives { ctxt with positive_ordinals = pos};
           (* need full subtype to rollback unification of variables if it fails *)
         let time = Timed.Time.save () in
         let prf =
           try
             let prf = subtype ctxt t a c0 in
             check_sub_proof prf;
             Io.log_sub "eq ok\n%!";
             if not (List.for_all (fun o1 ->
               List.exists (eq_ordinal ctxt.positive_ordinals o1)
                 ctxt.positive_ordinals) pos)
             then raise Exit;
             Io.log_typ "induction hyp applies with %d %a ~ %a <- %a:\n%!"
               fnum (print_kind false) a (print_kind false) c0
               print_positives { ctxt with positive_ordinals = pos};
             prf
           with Exit | Subtype_error _ | Error.Error _ ->
             Timed.Time.rollback time;
             raise Exit
         in
         add_call ctxt fnum ov true;
         Typ_YH(fnum,prf)
       with Exit -> fn hyps
  in
  (* HEURISTIC: try induction hypothesis with more parameters first.
     useful for flatten2 in lib/list.typ *)
  let hyps = List.sort (fun (_,_,_,both) (_,_,_,both') ->
    mbinder_arity both' - mbinder_arity both) hyps in
  fn hyps

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
    let proof_ptr = ref (-1, dummy_proof) in
    assert (!remains = []);
    remains := (ctxt, c0, proof_ptr) :: !remains;
    (* The main function doing the breadth-first search for the proof *)
    (* n : the current depth *)
    let depth = if has_leading_ord_quantifier c0 then depth + 1 else depth in
    breadth_first proof_ptr hyps_ptr f remains do_subsume depth

  (* we reach this point when we are call from type_check inside
     breadth_fitst above *)
  | Some ({contents = hyps }) ->
    try search_induction depth ctxt t a c0 hyps with Not_found ->
      (* No inductive hypothesis applies, we add a new induction hyp and
         record the unproved judgment with the other *)
      let ptr = ref (-1, dummy_proof) in
      Io.log_typ "adding remain at %d %a\n%!" depth (print_kind false) c0;
      remains := (ctxt, c0, ptr) :: !remains;
      Typ_TFix(ptr)

let subtype : ?ctxt:subtype_ctxt -> ?term:term -> kind -> kind -> sub_prf * calls_graph =
  fun ?ctxt ?term a b ->
    let term = unbox (generic_tcnst (box a) (box b)) in
    let ctxt =
      {  (empty_ctxt ()) with
          fun_table = init_fun_table ()
        ; calls = ref []
        ; delayed = ref []
        ; top_induction = (-1, [])
      }
    in
    let p = subtype ctxt term a b in
    List.iter (fun f -> f ()) !(ctxt.delayed);
    let calls = inline ctxt.fun_table !(ctxt.calls) in
    if not (sct ctxt.fun_table calls) then loop_error dummy_position;
    check_sub_proof p;
    (p, (ctxt.fun_table.table, calls))

let type_check : term -> kind option -> kind * typ_prf * calls_graph =
  fun t k ->
    let k = from_opt' k new_kuvar in
    let ctxt = empty_ctxt () in
    let (prf, calls) =
      try
        let p = type_check ctxt t k in
        check_typ_proof p;
        List.iter (fun f -> f ()) !(ctxt.delayed);
        let calls = inline ctxt.fun_table !(ctxt.calls) in
        if not (sct ctxt.fun_table calls) then loop_error t.pos;
        reset_all ();
        (p, (ctxt.fun_table.table, calls))
      with e -> reset_all (); raise e
    in
    let fn (v, os) =
      match !(v.uvar_state) with
      | Free   -> true
      | Sum  l ->
         let k = mbind_assoc kdsum v.uvar_arity l in
         safe_set_kuvar All v k os; false (* FIXME: should not trust safe_set *)
      | Prod l ->
         let k = mbind_assoc kprod v.uvar_arity l in
         safe_set_kuvar All  v k os ; false (* FIXME: should not trust safe_set *)
    in
    let ul = List.filter fn (kuvar_list k) in
    let ol = ouvar_list k in
    let k = List.fold_left (fun acc (v,_) -> KKAll (bind_kuvar v acc)) k ul in
    let k = List.fold_left (fun acc v -> KOAll (bind_ouvar v acc)) k ol in
    (k, prf, calls)

let try_fold_def : kind -> kind = fun k ->
  let save_debug = !Io.debug in
  Io.debug := "";
  let match_def k def =
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
    | k when has_uvar k -> k
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
