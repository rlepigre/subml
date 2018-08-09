(****************************************************************************)
(**{3                 Functions related to generalisation                  }*)
(****************************************************************************)

open LibTools
open Ast
open Compare
open Pos
open Bindlib
open Format
open Term
open Binding
open Print
open AstMap

(** Raised when generalisation is not a good idea.
    Currently when
    - KMRec and KNRec are present. *)
exception FailGeneralise

(** the type of a particular judgement, ordinal being witnesses or
    ordinal variables *)
type 'a particular = (int * ordi) list * ordi list * 'a * kind

(** function to apply a schema. I
    - If [general = false], it replace the ordinals with appropriate
      witnesses to prove the schema (not to use it).
    - If [general = true], we want to use the schema and all ordinals
      are replaced with variables *)
let recompose : ?general:bool -> schema -> term_or_kind particular =
  fun ?(general=true) ({ sch_posit = pos; sch_relat = rel; sch_judge = both } as schema) ->
    let res = ref [] in
    let forbidden = ref [] in
    let arity = mbinder_arity both in
    let rec search i =
      assert (i < arity && not (List.mem i !forbidden));
      try
        List.assoc i !res
      with Not_found ->
        forbidden := i::!forbidden;
        let o =
          if general then
            try
              let v = search (List.assoc i rel) in
              new_ouvar ~upper:(constant_mbind 0 v) ()
            with Not_found ->
              new_ouvar ()
          else
             let o' = try search (List.assoc i rel) with Not_found -> OMaxi in
             OLess(o',Gen(i,schema))
        in
        res := (i, o) :: !res;
        forbidden := List.tl !forbidden;
        o
    in
    let ovars = Array.init arity search in
    let (k1, k2) = msubst both ovars in
    let pos = List.map (fun i -> assert (i < arity); ovars.(i)) pos in
    let os = Array.to_list (Array.mapi (fun i x -> (i,x)) ovars) in
    Io.log_sub "recompose os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
      Format.fprintf ff "(%d,%a) "n (print_ordi false) o) l) os;

    os, pos, k1, k2

(** recompose for subtyping *)
let recompose_kind : ?general:bool -> schema -> kind particular =
  fun ?(general=true) schema ->
    let (os,pos,k1,k2) = recompose ~general schema in
    let k1 = match k1 with
      | SchTerm _ -> assert false (* Should not happen. *)
      | SchKind k -> k
    in (os,pos,k1,k2)

(** recompose for typing *)
let recompose_term : ?general:bool -> schema -> unit particular =
  fun ?(general=true) schema ->
    let (os,pos,t,k2) = recompose ~general schema in
    let t = match t with
      | SchTerm t -> ()
      | SchKind _ -> assert false (* Should not happen. *)
    in (os,pos,t,k2)

(** [generalise] create a schema from a judgement. All ordinals
    that appear in the judgement are quantified over.
    Ordinal appearing in witnesses are untouched.

    Each ordinal as an index used to denote it in the field
    [sch_posit] and [sch_relat], to know which ordinals are positive,
    or comparable with '<'.

    This index is the same as the index in the mbinder [sch_judge]
    It returns the index of the original variable.

    It also returns the index of the original ordinals to build
    the initial call in the call graph.

    Finaly in calls [recompose ~genralise:false] to build the
    instance of the schema with the witnesses that is needed to
    prove the schema.
 *)
let generalise : ?manual:bool -> ordi list -> term_or_kind -> kind
                 -> Sct.t -> schema * (int * ordi) list =
  fun ?(manual=false) pos k1 k2 call_table ->

  (* will of the table of all ordinals in the type to generalize them.
     the ordinal will be ovari when it replaces an infinite ordinals
     (see TODO in bind_fn and bind_gn.

     The integer, is a temporary index, The variable is the future
     variable to be bound using bind_fn The boolean ref is to know if
     the variable occurs in the formula *)

  let res : (ordi * (int * ovar * bool ref)) list ref = ref [] in
  (* counter for the index above *)
  let i = ref 0 in
  (* This table will keep the relation (o, o') when o = OLess(o',_) *)
  let relation : (int * int) list ref = ref [] in
  (* a name for the Sct do distinguish subtyping and typing schema *)
  let name = match k1 with SchKind _ -> "S" | SchTerm f -> binder_name f in

  (* function to add an OLess ordinal in the table of all ordinal res
     We also keep in relation, the relation between OLess ordinal

     The references k in res are set to true as soon as we have an
     occurrence of the ordinal not inside a witness.
   *)
  let rec eps_search keep o =
    match orepr o with
    | OLess(o',w) ->
       (try
          let (n,v,k) = assoc_ordi o !res in
          k := !k || keep;
          (n,o)
        with
          Not_found ->
            let n = !i in incr i;
            let v = new_ovari ("o_" ^ string_of_int n) in
            res := (o, (n, v, ref keep)) :: !res;
            if o' <> OMaxi && o' <> OConv then (
                let (p, _) = eps_search false o' in
                relation := (n,p)::!relation);
            (n, o))
    | o ->
       Io.err "==> %a <==\n%!" (print_ordi true) o;
       assert false
  in

  (* function to map type and ordinals, at this stage, we register all
     ordinals with eps_search, except ordinals in witnesses.  If
     manual = false, we also replace negative OConv with fresh ordinal
     variables to produce a more general schema.

     We can not immediatly replace OLess by variables, because
     ordinals that appears only in witnesses must not be replaced, but
     ordinals that appears both in witnesses and outside must be
     replaced everywhere. Therefore two descents in the trees are
     necessary.

     We also fix the value of unification variables when they have
     constraints because schema with unification variables are
     problematic.
  *)
  let ford occ o (self_kind:self_kind) (self_ord:self_ord) def_ord =
    let o = orepr o in
    let res =
      match o with
      | OLess _ when occ <> Non ->
         assert(match occ with Reg _ -> false | _ -> true);
         let (_, o) = eps_search true o in box o
      | OUVar(u,os) -> (* NOTE: avoid looping in flot.typ/compose *)
         if ouvar_use_state self_ord pos u os then
           self_ord o
         else
           def_ord o
      | OConv when occ = sNeg && not manual ->
         let n = !i in incr i;
         let v = new_ovari ("o_" ^ string_of_int n) in
         res := (mk_free_o v, (n, v, ref true)) :: !res; box_of_var v
      | o -> def_ord o
    in
    res
  in
  let fkind occ k (self_kind:self_kind) (self_ord:self_ord) def_kind =
    match full_repr k with
    | KMRec(_,k)
    | KNRec(_,k) -> raise FailGeneralise
      (* NOTE:Lets unroll once more to propagate positiveness infos *)
    | KDefi(td,os,ks) -> assert false
      (* TODO: should not open definition if the definition has no mu/nu *)
    | KUCst(t,f,cl) | KECst(t,f,cl) ->
       if cl then box k else map_kind k (* NOTE: no generalization in witness *)
    | KUVar(v,os) as k -> (* FIXME: duplicated code in type_infer *)
       if uvar_use_state v os then self_kind k else def_kind k
    | k -> def_kind k

  in
  (* we now map k1 and k2 *)
  let k1 = match k1 with
    | SchKind k1 -> SchKind (unbox (map_kind ~fkind ~ford ~occ:sNeg k1))
    | SchTerm _  -> k1
  in
  let k2 = unbox (map_kind ~fkind ~ford ~occ:sPos k2) in

  (* we also collect information about positive ordinals *)
  let pos = List.map (fun o -> fst (eps_search false o)) pos in

  (* we keep only the ordinals that are not under witnesses *)
  let res = List.filter (fun (o,(n,v,k)) -> !k) !res in

  (* we collect the corresponding variables and ordinals *)
  let ovars = Array.of_list (List.map (fun (o,(n,v,_)) -> v) res) in
  let ords  = Array.of_list (List.map (fun (o,(n,v,_)) -> o) res) in
  Io.log_uni "bind in generalise\n%!";

  (* and now we really bind the generaliszed ordinals *)
  let k1 = match k1 with
    | SchKind k1 ->
       box_apply (fun k -> SchKind k)
         (bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k1)
    | SchTerm _  -> box k1
  in
  let k2 = bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k2 in
  let both = box_pair k1 k2 in
  let both = unbox (bind_mvar ovars both) in

  (* in the schema, the positibe ordinals and relation are given by integer,
     so we build a table giving the position of each bound ordinals in
     the schema *)
  let tbl = List.mapi (fun i (o,(n,v,k)) -> (n,i)) res in
  (* we also build the list of ordinals by index, as it is needed to
     build the call matrix for the sct *)
  let os = List.mapi (fun i (o,_) -> (i, o)) res in

  (* this function apply trasitivity in the relation to ignore intermediate
     ordinals that are not bound *)
  let rec next start n =
    if List.exists (fun (q,_) -> n = q) tbl then n else
      try
        let l = List.find_all (fun (n',_) -> n = n') !relation in
        assert (List.length l <= 1);
        let n = List.assoc n l in
        next false n
      with Not_found -> n
  in

  (* we now build the list of positive ordinals for the schema,
     first we apply next (because o1 < o2 and o1 positive
     imply o2 positibe *)
  let pos = List.map (next true) pos in
  (* we keep only the bound ordinals *)
  let pos = List.filter (fun n -> List.exists (fun (q,_) -> n = q) tbl) pos in
  (* we replace the ordinals initial index by their final index *)
  let pos = List.map (fun n -> List.assoc n tbl) pos in
  (* we sort for easier equality test on schema *)
  let pos = List.sort_uniq (-) pos in

  (* we do the same for relation *)
  let rel = List.map (fun (n,p) -> (n, next true p)) !relation in
  let rel = List.filter (fun (n,p) ->
    List.exists (fun (q,_) -> n = q) tbl && List.exists (fun (q,_) -> p = q) tbl) rel in
  let rel = List.map (fun (n,p) -> List.assoc n tbl, List.assoc p tbl) rel in
  let rel = List.sort_uniq (fun (x,y) (x',y') -> x - x') rel in

  Io.log_sub "generalise pos: %a\n%!"
    (fun ff l -> List.iter (Format.fprintf ff "%d ") l) pos;
  Io.log_sub "generalise rel: %a\n%!"
    (fun ff l -> List.iter (fun (a,b) ->
    Format.fprintf ff "(%d,%d) "a b) l) rel;
  Io.log_sub "generalise os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
    Format.fprintf ff "(%d,%a) "n (print_ordi false) o) l) os;

  (* we ask a new function index to the sct module *)
  let fnum = Sct.create_symbol call_table name (Bindlib.mbinder_names both) in
  (* we can now build the final schema *)
  let schema =
    { sch_index = fnum
    ; sch_posit = pos
    ; sch_relat = rel
    ; sch_judge = both
    }
  in
  (schema, os)

let generalise : ?manual:bool -> ordi list -> term_or_kind -> kind
                 -> Sct.t -> (schema * (int * ordi) list) option =
  fun ?manual pos k1 k2 call_table ->
    try Some(generalise ?manual pos k1 k2 call_table)
    with FailGeneralise -> None



(** Returns the list of unification variables.
    When a variable has arguments, they should be identical
    for all occurences. *)
let kuvar_list : kind -> (kuvar * ordi array) list = fun k ->
  let r = ref [] in
  let adone = ref [] in
  let rec fn k =
    let k = repr k in
    if List.memq k !adone then () else (
    adone := k::!adone;
    match k with
    | KFunc(a,b)   -> fn a; fn b
    | KProd(ls,_)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f kdummy)
    | KFixM(o,f)
    | KFixN(o,f)   -> fn (subst f kdummy)
    | KOAll(f)
    | KOExi(f)     -> fn (subst f odummy)
    | KUVar(u,os)  ->
       begin
         match uvar_state u with
         | Free -> ()
         | DSum l | Prod l ->
            List.iter (fun (c,f) -> fn (msubst f (Array.make (mbinder_arity f) odummy))) l
       end;
       if not (List.exists (fun (u',_) -> eq_uvar u u') !r) then
         r := (u,os) :: !r
    | KDefi(d,_,a) -> Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f kdummy)
    | KPrnt _ -> assert false)
  in
  fn k; !r

(** Same as above for ordinal variables *)
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
    | KProd(ls,_)
    | KDSum(ls)    -> List.iter (fun (_,a) -> fn a) ls
    | KKAll(f)
    | KKExi(f)     -> fn (subst f kdummy)
    | KFixM(o,f)
    | KFixN(o,f)   -> gn o; fn (subst f kdummy)
    | KOAll(f)
    | KOExi(f)     -> fn (subst f odummy)
    | KDefi(d,o,a) -> Array.iter gn o;  Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl)-> fn (subst f kdummy)
    | KPrnt _      -> assert false)
  and gn o =
    match orepr o with
    | OSucc(o)   -> gn o
    | OUVar(v,_) -> if not (List.exists (eq_uvar v) !r) then r := v :: !r
    | OConv      -> ()
    | OMaxi      -> ()
    | OLess _    -> ()
    | OVari _    -> ()
    | OVars _    -> assert false
  in
  fn k; !r
