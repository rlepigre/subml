(****************************************************************************)
(**{3            Data structure and basic functions for typing             }*)
(****************************************************************************)


(** Main function for typing and subtyping *)
open Bindlib
open Ast
open Binding
open Print
open Position
open Compare
open Term
open Generalise
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

exception Interrupted of pos
let interrupted : pos -> 'a =
  fun p -> raise (Interrupted p)

type induction_node = Sct.index * (int * ordinal) list
type subtype_ctxt =
  { sub_induction_hyp : sub_induction list
  ; fix_induction_hyp : fix_induction list
  ; top_induction     : induction_node
  ; call_graphs       : Sct.call_table
  ; positive_ordinals : ordinal list }

(** induction hypothesis for subtyping *)
and sub_induction =
      Sct.index            (** the index of the induction hyp *)
    * int list             (** the positivity context *)
    * (int * int) list     (** the relation between ordinals *)
    * (ordinal, kind * kind) mbinder (** the two kinds *)

(** induction hypothesis for typing recursive programs *)
and fix_induction =
      (term',term) binder     (* the argument of the fixpoint combinator *)
    * kind                    (* the initial type, if no initial ordinal params *)
              (* the induction hypothesis collected so far for this fixpoint *)
    * (Sct.index              (* reference of the inductive hyp *)
       * int list             (** the positivity context *)
       * (int * int) list     (** the relation between ordinals *)
       * (ordinal, kind * kind) mbinder) (** the kind, ignore the first *)
      list ref
    * (subtype_ctxt * kind * (Sct.index * typ_prf) ref) list ref
      (* The use of references here is to do a breadth-first search for
         inductive proof. Depth first here is bad, using too large depth.
         The reference holds proofs yet to be done *)

(** the initial empty context *)
let empty_ctxt () =
  { sub_induction_hyp = []
  ; fix_induction_hyp = []
  ; top_induction = (Sct.root, [])
  ; call_graphs = Sct.init_table ()
  ; positive_ordinals = [] }


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
      Io.log_mat "  compare %d %a <=? %d %a => %!" i (print_ordinal false) o
        j (print_ordinal false) o';
      let r =
        if less_ordinal pos o o' then Less
        else if leq_ordinal pos o o' then Leq
        else Unknown
      in
      Io.log_mat "%a\n%!" prCmp r;
      assert(j < l);
      assert(i < c);
      m.(j).(i) <- r
    ) a) b;
  m

let consecutive =
  let rec fn n = function
    | [] -> true
    | (p,_)::l when n = p -> fn (n+1) l
    | _ -> false
  in fn 0

let add_call ctxt fnum os is_induction_hyp =
  let open Sct in
  let pos = ctxt.positive_ordinals in
  let calls = ctxt.call_graphs in
  let cur, os0 = ctxt.top_induction in
  assert(consecutive os);
  assert(consecutive os0);
  Io.log_mat "adding call %a -> %a\n%!" prInd cur prInd fnum;
  let m = find_indexes calls pos fnum cur os os0 in
  let call = (fnum, cur, m, is_induction_hyp) in
  Sct.new_call calls call

(** construction of an ordinal < o such that w *)
let rec opred o w =
  let o = orepr o in
  match o with
  | OSucc o' -> o'
  | OUVar({uvar_state = (None,None); uvar_arity = a} as p, os) ->
     let o' = OUVar(new_ouvara a,os) in
     set_ouvar p (obind_ordinals os (OSucc o')); o'
  | OUVar({uvar_state = (Some o',None); uvar_arity = a} as p, os) ->
     set_ouvar p o'; opred o w
  | OUVar _ -> type_error "opred fails"; (* FIXME: can we do better ? *)
  | OVari _ -> assert false
  | OLess _ | OConv -> OLess(o, w)

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
  | OVari _ -> assert false
  | o ->
     if not (fn 0 o) then raise Not_found;
     new_ouvar ~upper:(constant_mbind 0 o) ()

let is_positive ctxt o =
  match orepr o with
  | OConv | OSucc _ -> true
  | OVari _ -> assert false
  | o ->
     List.exists (fun o' -> eq_ordinal ctxt.positive_ordinals o' o)
       ctxt.positive_ordinals

   let rec dot_proj t k s = match full_repr k with
  | KKExi(f) ->
     let c = KECst(t,f,true) in (* NOTE: used only for close term *)
     if binder_name f = s then c else dot_proj t (subst f c) s
  | k ->
     raise Not_found
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
     if List.exists (strict_eq_ordinal o) positives
     then positives else o :: positives

let add_positive ctxt o =
  { ctxt with positive_ordinals = add_pos ctxt.positive_ordinals o }

let add_positives ctxt gamma =
  let positive_ordinals =
    List.fold_left add_pos ctxt.positive_ordinals gamma
  in
  { ctxt with positive_ordinals }

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
