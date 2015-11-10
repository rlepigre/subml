open Bindlib
open Util
open Ast

exception Type_error of pos * string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype : term -> kind -> kind -> unit = fun t a b ->
  if a == b then () else
  assert false

let rec type_check : term -> kind -> unit = fun t c ->
  match t.elt with
  | Coer(t,a) ->
      subtype t a c;
      type_check t a
  | LVar(x) ->
      type_error t.pos "Cannot type-check open terms..."
  | LAbs(ao,f) ->
      let a = match ao with None -> new_uvar () | Some a -> a in
      let b = new_uvar () in
      let c' = Func(a,b) in
      subtype t c' c;
      type_check (subst f (cnst (binder_name f) a b)) c'
  | Appl(t,u) ->
      let a = new_uvar () in
      type_check t (Func(a,c));
      type_check u a
  | Reco(fs) ->
      let ts = List.map (fun (x,_) -> (x, new_uvar ())) fs in
      subtype t (Prod(ts)) c;
      let check (l,t) =
        let cl = List.assoc l ts in
        type_check t cl
      in
      List.iter check fs
  | Proj(t,l) ->
      let c' = Prod([(l,c)]) in
      type_check t c'
  | VDef(v) ->
      begin
        match v.ttype with
        | Some a -> subtype v.value a c
        | None   -> type_check v.value c
      end
  | Prnt(_,t) ->
      type_check t c
  | FixY ->
      subtype t (unbox (fall' "X" (fun x -> func (func (func x x) x) x))) c
  | Cnst(cst) ->
      let (_,a,_) = cst in
      subtype t a c

let type_infer : term -> kind = fun t ->
  let a = new_uvar () in
  type_check t a; repr a
