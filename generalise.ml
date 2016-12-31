(****************************************************************************)
(**{3                 Functions related to generalisation                  }*)
(****************************************************************************)

open Ast
open Compare
open Position
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
type particular = (int * ordi) list * ordi list * kind * kind

(** function to apply a schema. I
    - If [general = false], it replace the ordinals with appropriate
      witnesses to prove the schema (not to use it).
    - If [general = true], we want to use the schema and all ordinals
      are replaced with variables *)
let recompose : ?general:bool -> schema -> particular =
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
             let o' = try search (List.assoc i rel) with Not_found -> OConv in
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
let generalise : ordi list -> kind -> kind -> Sct.call_table ->
  schema * (int * ordi) list * particular
  = fun pos k1 k2 call_table ->

  (* will of the table of all ordinals in the type to generalize them.
     the ordinal will be ovari when it replaces an infinite ordinals (see TODO
     in bind_fn and bind_gn.

     The integer, is a temporary index,
     The variable is the future variable to be bound using bind_fn
     The boolean ref is to know if the variable occurs in the formula *)

  let res : (ordi * (int * ovar * bool ref)) list ref = ref [] in
  (* ocunter for the index above *)
  let i = ref 0 in
  (* This table will keep the relation (o, o') when o = OLess(o',_) *)
  let relation : (int * int) list ref = ref [] in

  let rec eps_search keep o =
    match o with
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
            if o' <> OConv then (
                let (p, _) = eps_search false o' in
                relation := (n,p)::!relation);
            (n, o))
    | o -> assert false
  and ford occ o (self_kind:self_kind) (self_ord:self_ord) def_ord =
    let o = orepr o in
    let res =
      match o with
      | OLess _ -> let (_, o) = eps_search true o in box o
      | OUVar({uvar_state = (Some o', _)} as u, os) when occ = Pos ->
         set_ouvar u o'; self_ord ~occ o (* NOTE: avoid looping in flot.typ/compose *)
      | OConv when occ = Neg ->
         let n = !i in incr i;
         let v = new_ovari ("o_" ^ string_of_int n) in
         res := (free_of v, (n, v, ref true)) :: !res; box_of_var v
      | o -> def_ord o
    in
    res
  and fkind occ k (self_kind:self_kind) (self_ord:self_ord) def_kind =
    match full_repr k with
    | KMRec(_,k)
    | KNRec(_,k) -> raise FailGeneralise
      (* NOTE:Lets unroll once more to propagate positiveness infos *)
    | KDefi(td,os,ks) -> assert false
      (* TODO: should not open definition if the definition has no mu/nu *)
    | KUCst(t,f,cl) | KECst(t,f,cl) ->
       if cl then box k else map_kind k (* NOTE: no generalization in witness *)
    | k -> def_kind k

  in
  let k1 = unbox (map_kind ~fkind ~ford ~occ:Neg k1) in
  let k2 = unbox (map_kind ~fkind ~ford ~occ:Pos k2) in

  let pos = List.map (fun o -> fst (eps_search false o)) pos in
  let res = List.filter (fun (o,(n,v,k)) -> !k) !res in
  let ovars = Array.of_list (List.map (fun (o,(n,v,_)) -> v) res) in
  let ords  = Array.of_list (List.map (fun (o,(n,v,_)) -> o) res) in
  Io.log_uni "bind in generalise\n%!";
  let k1 = bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k1 in
  let k2 = bind_fn ~from_generalise:true ords (Array.map box_of_var ovars) k2 in
  let both = box_pair k1 k2 in
  let both = unbox (bind_mvar ovars both) in
  let tbl = List.mapi (fun i (o,(n,v,k)) -> (n,i)) res in
  let os = List.map (fun (o,(n,v,_)) -> (List.assoc n tbl, o)) res in

  let rec next start n =
    if List.exists (fun (q,_) -> n = q) tbl then n else
      try
        assert (List.length (List.find_all (fun (n',_) -> n = n') !relation) <= 1);
        let n = List.assoc n !relation in
        next false n
      with Not_found -> n
  in

  let pos = List.map (next true) pos in
  let pos = List.sort_uniq (-) pos in
  let pos = List.filter (fun n -> List.exists (fun (q,_) -> n = q) tbl) pos in
  let pos = List.map (fun n -> List.assoc n tbl) pos in

  let rel = List.map (fun (n,p) -> (n, next true p)) !relation in
  let rel = List.filter (fun (n,p) ->
    List.exists (fun (q,_) -> n = q) tbl && List.exists (fun (q,_) -> p = q) tbl) rel in
  let rel = List.map (fun (n,p) -> List.assoc n tbl, List.assoc p tbl) rel in

  Io.log_sub "generalise pos: %a\n%!"
    (fun ff l -> List.iter (Format.fprintf ff "%d ") l) pos;
  Io.log_sub "generalise rel: %a\n%!"
    (fun ff l -> List.iter (fun (a,b) ->
    Format.fprintf ff "(%d,%d) "a b) l) rel;
  Io.log_sub "generalise os : %a\n%!" (fun ff l -> List.iter (fun (n,o) ->
    Format.fprintf ff "(%d,%a) "n (print_ordi false) o) l) os;

  assert(mbinder_arity both = List.length os);
  (* "Y" for typing, "S" for subtyping *)
  let schema =
    { sch_index = Sct.root
    ; sch_posit = pos
    ; sch_relat = rel
    ; sch_judge = both
    }
  in
  let (os0,tpos,k1,k2) = recompose ~general:false schema in
  let name = if strict_eq_kind k1 (KProd []) then "Y" else "S" in
  let fnum = Sct.new_function call_table name
    (List.map Print.ordi_to_printer os0)
  in
  let schema = { schema with sch_index = fnum } in
  (schema, os, (os0,tpos,k1,k2))

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
         | DSum l | Prod l ->
            List.iter (fun (c,f) -> fn (msubst f (Array.make (mbinder_arity f) OConv))) l
       end;
       if not (List.exists (fun (u',_) -> eq_uvar u u') !r) then
         r := (u,os) :: !r
    | KDefi(d,_,a) -> Array.iter fn a
    | KMRec _
    | KNRec _      -> assert false
    | KVari _      -> ()
    | KUCst(_,f,cl)
    | KECst(_,f,cl) -> fn (subst f (KProd []))
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
    | KECst(_,f,cl)-> fn (subst f (KProd []))
    | KPrnt _      -> assert false)
  and gn o =
    match orepr o with
    | OSucc(o)   -> gn o
    | OUVar(v,_) -> if not (List.exists (eq_uvar v) !r) then r := v :: !r
    | OConv      -> ()
    | OLess _    -> ()
    | OVari _    -> ()
    | OVars _    -> assert false
  in
  fn k; !r
