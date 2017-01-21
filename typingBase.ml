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
open Term
open Error
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

exception Interrupted of popt
let interrupted : popt -> 'a =
  fun p -> raise (Interrupted p)

type induction_node = Sct.index * (int * ordi) list
type ctxt =
  { sub_ihs       : schema list
  ; fix_ihs       : fix_induction list
  ; fix_todo      : (unit -> unit) list ref
  ; top_induction : induction_node
  ; call_graphs   : Sct.call_table
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
  ; call_graphs   = Sct.init_table ()
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
  Io.log_mat "build matrix for %a %a\n" prInd index prInd index';
  let c = arity index ftbl and l = arity index' ftbl in
  let m = Array.init l (fun _ -> Array.make c Unknown) in
  List.iteri (fun j (j',o') ->
    assert(j=j');
    List.iteri (fun i (i',o) ->
      assert(i=i');
      Io.log_mat "  compare %d %a <=? %d %a => %!" i (print_ordi false) o
        j (print_ordi false) o';
      let r =
        if less_ordi pos o o' then Less
        else if leq_ordi pos o o' then Leq
        else Unknown
      in
      Io.log_mat "%a\n%!" prCmp r;
      assert(j < l);
      assert(i < c);
      m.(j).(i) <- r
    ) a) b;
  m

let score_mat m =
  let open Sct in
  let nb_lines = Array.length m in
  let nb_colos = if nb_lines > 0 then Array.length m.(0) else 0 in
  let less = ref 0 in
  let leq  = ref 0 in
  for i = 0 to nb_lines - 1 do
    let found_less = ref false and found_leq = ref false in
    for j = 0 to nb_colos - 1 do
      match m.(i).(j) with
      | Less -> found_less := true
      | Leq  -> found_leq := true
      | _    -> ()
    done;
    if !found_less then incr less
    else if !found_leq then incr leq
  done;
  (float !less /. float nb_colos, float !leq /. float nb_colos)

let consecutive =
  let rec fn n = function
    | [] -> true
    | (p,_)::l when n = p -> fn (n+1) l
    | _ -> false
  in fn 0

let build_call ctxt fnum os is_induction_hyp =
  let open Sct in
  let pos = ctxt.non_zero in
  let calls = ctxt.call_graphs in
  let cur, os0 = ctxt.top_induction in
  assert(consecutive os);
  assert(consecutive os0);
  Io.log_mat "adding call %a -> %a\n%!" prInd cur prInd fnum;
  let m = find_indexes calls pos fnum cur os os0 in
  fnum, cur, m, is_induction_hyp

let add_call ctxt fnum os is_induction_hyp =
  let call = build_call ctxt fnum os is_induction_hyp in
  Sct.new_call ctxt.call_graphs call

(** If w = Some w': construction of an ordinal < o such that w
    If w = None: find an ordinal o' < o *)
let rec opred : ordi -> ord_wit option -> ordi = fun o w ->
  let o = orepr o in
  match o, w with
  | OSucc o', _ -> o'
  | OUVar({uvar_state = {contents = Unset (None,None)}; uvar_arity = a} as p, os), _ ->
     let o' = OUVar(new_ouvara a,os) in
     set_ouvar p (obind_ordis os (OSucc o')); o'
  | OUVar({uvar_state = {contents = Unset (Some o', _)}; uvar_arity = a} as p, os), _ ->
     set_ouvar p o'; opred o w
  | OConv, None -> OConv
  | (OLess _ | OUVar _) as o, None -> new_ouvar ~upper:(constant_mbind 0 o) ()
  | OUVar _, Some w ->
     subtype_error "opred fails"; (* FIXME: can we do better ? OLess(o,w)
     has an invariant that o is itself OLess or OConv ? *)
  | (OConv | OLess _ as o), Some w ->
     OLess(o, w)
  | (OVari _ | OVars _), _ -> assert false

(** give a list of positive ordinals that may be equal to o.
    This list is of legth >= 2 only if o is an OUVar *)
let possible_positive ctxt o =
  let pos = ctxt.non_zero in
  let res = match orepr o with
  | OConv -> [OConv]
  | OSucc o' -> [o]
  | OUVar(u,os) ->
     let l = List.filter
       (fun o ->
         Io.log_sub "testing %a\n%!" (print_ordi false) o;
         Timed.pure_apply (less_opt_ordi pos o (uvar_state u)) os) ctxt.non_zero
     in
     let l =
       if l = [] then
         let o' = OSucc (new_ouvar ()) in
         if Timed.pure_apply (less_opt_ordi pos o' (uvar_state u)) os then
           [o']
         else []
       else l
     in
     let l =
       if Timed.pure_apply (less_opt_ordi pos OConv (uvar_state u)) os then
         l @ [OConv]
       else l
     in
     l
  | OLess _ as o -> if is_positive ctxt.non_zero o then [o] else []
  | OVari _ | OVars _ -> assert false
  in
  Io.log_sub "possible positive: %a ==> %a\n%!" (print_ordi false) o
    (print_list (print_ordi false) ",") res
  ;
  res

let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in (* NOTE: used only for close term *)
     if binder_name f = s then c else dot_proj t (subst f c) s
  | k ->
     raise Not_found
(* FIXME: end of the function which certainly miss cases *)

let print_nz ff ctxt =
  let p_aux = print_ordi false in
  match ctxt.non_zero with
      | [] -> ()
      | l -> Io.log "  (%a)\n\n%!" (print_list p_aux ", ") l

let rec add_pos positives o =
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
    | KUVar(_) -> raise Exit
    | KDefi(d,o,a) -> Array.iter fn a
    | KMRec(_,k)
    | KNRec(_,k) -> fn k
    | KVari _    -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd []))
    | KPrnt _    -> assert false
  in
  try
    fn k; false
  with
    Exit -> true
