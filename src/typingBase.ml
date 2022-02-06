(****************************************************************************)
(**{3            Data structure and basic functions for typing             }*)
(****************************************************************************)


(** Main function for typing and subtyping *)
open Bindlib
open Ast
open Binding
open Print
open Pos
open Compare
open LibTools

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
exception Loop_error of popt
let loop_error : popt -> 'a =
  fun p -> raise (Loop_error p)

type induction_node = Sct.index * (int * ordi) list
type ctxt =
  { sub_ihs       : schema list
  ; fix_ihs       : fix_induction list
  ; fix_todo      : (unit -> unit) list ref
  ; top_induction : induction_node
  ; call_graphs   : Sct.t
  ; non_zero      : ordi list }

(** induction hypothesis for typing recursive programs *)
and fix_induction = (term',term) binder * schema list ref
(* Contains the the argument of the fixpoint combinator and the induction
   hypotheses collected so far for this fixpoint. *)

(** the initial empty context *)
let empty_ctxt () =
  { sub_ihs       = []
  ; fix_ihs       = []
  ; fix_todo      = ref []
  ; top_induction = (Sct.root, [])
  ; call_graphs   = Sct.create ()
  ; non_zero      = [] }

(** run the registered functions. *)
let rec run_fix_todo : ctxt -> unit = fun ctxt ->
  match !(ctxt.fix_todo) with
  | [] -> ()
  | ls -> ctxt.fix_todo := [];
          List.iter (fun f -> f ()) ls;
          run_fix_todo ctxt

(****************************************************************************
 *                               SCT functions                              *
 ****************************************************************************)

let find_indexes ftbl pos index index' a b =
  let open Sct in
  Io.log_mat "build matrix for %d %d\n"
    (int_of_index index) (int_of_index index');
  let w = arity index  ftbl in
  let h = arity index' ftbl in
  let tab = Array.init h (fun _ -> Array.make w Infi) in
  List.iteri (fun j (j',o') ->
    assert(j=j');
    List.iteri (fun i (i',o) ->
      assert(i=i');
      Io.log_mat "  compare %d %a <=? %d %a => %!" i (print_ordi false) o
        j (print_ordi false) o';
      let r =
        if less_ordi pos o o' then Min1
        else if leq_ordi pos o o' then Zero
        else Infi
      in
      Io.log_mat "%s\n%!" (cmp_to_string r);
      assert(j < h);
      assert(i < w);
      tab.(j).(i) <- r
    ) a) b;
  {w; h; tab}

let consecutive =
  let rec fn n = function
    | [] -> true
    | (p,_)::l when n = p -> fn (n+1) l
    | _ -> false
  in fn 0

let build_call ctxt callee os is_rec =
  let open Sct in
  let pos = ctxt.non_zero in
  let calls = ctxt.call_graphs in
  let caller, os0 = ctxt.top_induction in
  assert(consecutive os);
  assert(consecutive os0);
  Io.log_mat "adding call %d -> %d\n%!"
    (int_of_index caller) (int_of_index callee);
  let matrix = find_indexes calls pos callee caller os os0 in
  {callee; caller; matrix; is_rec}

let add_call ctxt fnum os is_rec =
  let call = build_call ctxt fnum os is_rec in
  Sct.add_call ctxt.call_graphs call

(** construction of an ordinal < o such that w *)
let rec opred : ordi -> ord_wit -> ordi = fun o w ->
  let o = orepr o in
  match o with
  | OSucc o' -> o'
  | OUVar({uvar_state = {contents = Unset (None,None)}; uvar_arity = a; _} as p, os) ->
     let o' = OUVar(new_ouvara a,os) in
     assert (safe_set_ouvar [] p os (OSucc o')); o'
  | OUVar({uvar_state = {contents = Unset (Some o', _)}; uvar_arity = _; _} as p, os)
                                                   when not (ouvar_mbind_occur p o' os) ->
     set_ouvar p o'; opred o w
  | OUVar _ ->
     subtype_error "opred fails"; (* FIXME: can we do better ? OLess(o,w)
     has an invariant that o is itself OLess or OConv ? *)
  | (OConv | OLess _ as o) ->
     OLess(o, w)
  | OMaxi | OVari _ | OVars _ -> assert false

(** find an ordinal o' < o *)
let rec ofindpred : ctxt -> ordi -> ordi = fun ctxt o ->
  let o = orepr o in
  let pos = ctxt.non_zero in
  match o with
  | OSucc o' -> o'
  | OConv -> o
  | OLess _ as o ->
     if is_positive pos o then new_ouvar ~upper:(constant_mbind 0 o) ()
                          else raise Not_found
  | OUVar(u,os) ->
    (* find a positive ordinal that may be equal to an OUVar(u,os) *)
    let o' =
      try List.find
            (fun o ->
              Io.log_sub "testing %a\n%!" (print_ordi false) o;
              Timed.pure_apply (less_opt_ordi pos o (uvar_state u)) os) pos
      with Not_found ->
        let o' = OSucc (new_ouvar ()) in
        if Timed.pure_apply (less_opt_ordi pos o' (uvar_state u)) os then
          o'
        else if Timed.pure_apply (less_opt_ordi pos OConv (uvar_state u)) os then
          OConv
        else raise Not_found
    in
    set_ouvar u (obind_ordis os o');
    ofindpred ctxt o
  | OMaxi | OVari _ | OVars _ -> assert false

let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in (* NOTE: used only for close term *)
     if binder_name f = s then c else dot_proj t (subst f c) s
  | _ ->
     raise Not_found
(* FIXME: end of the function which certainly miss cases *)

let print_nz _ ctxt =
  let p_aux = print_ordi false in
  match ctxt.non_zero with
      | [] -> ()
      | l -> Io.log "  (%a)\n\n%!" (print_list p_aux ", ") l

let add_pos positives o =
  let o = orepr o in
  match o with
  | OConv | OSucc _ -> positives
  | _ ->
     if List.exists (strict_eq_ordi o) positives
     then positives else o :: positives

let add_positive ctxt o =
  { ctxt with non_zero = add_pos ctxt.non_zero o }

let add_positives ctxt gamma =
  let non_zero =
    List.fold_left add_pos ctxt.non_zero gamma
  in
  { ctxt with non_zero }

(* These three functions are only used for heuristics *)
let has_leading_ord_quantifier : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(_,b) -> fn b
    | KProd(ls,_)
    | KDSum(ls)  -> List.exists (fun (_,a) -> fn a) ls
    | KOAll(_)
    | KOExi(_)   -> true
    | KKAll(f)
    | KKExi(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f kdummy)
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | _ -> false
  in
  fn k

(* These three functions are only used for heuristics *)
let has_leading_exists : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(_,_) -> false
    | KProd(ls,_)
    | KDSum(ls)  -> List.exists (fun (_,a) -> fn a) ls
    | KKExi(_)
    | KOExi(_)   -> true
    | KOAll(f)   -> fn (subst f odummy)
    | KKAll(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f kdummy)
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | _ -> false
  in
  fn k

let has_leading_forall : kind -> bool = fun k ->
  let rec fn k =
    match full_repr k with
    | KFunc(_,_) -> false
    | KProd(ls,_)
    | KDSum(ls)  -> List.exists (fun (_,a) -> fn a) ls
    | KKAll(_)
    | KOAll(_)   -> true
    | KOExi(f)   -> fn (subst f odummy)
    | KKExi(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f kdummy)
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | _ -> false
  in
  fn k

let has_uvar : kind -> bool = fun k ->
  let rec fn k =
    match repr k with
    | KFunc(a,b) -> fn a; fn b
    | KProd(ls,_)
    | KDSum(ls)  -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)
    | KFixM(_,f)
    | KFixN(_,f) -> fn (subst f kdummy)
    | KOAll(f)
    | KOExi(f)   -> fn (subst f odummy)
    | KUVar(_) -> raise Exit
    | KDefi(_,_,a) -> Array.iter fn a
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | KVari _    -> ()
    | KUCst(_,f,_)
    | KECst(_,f,_) -> fn (subst f kdummy)
    | KPrnt _    -> assert false
  in
  try
    fn k; false
  with
    Exit -> true
