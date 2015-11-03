open Bindlib
open Util
open Ast

exception Type_error of pos * string

let type_error : pos -> string -> unit = fun p msg ->
  raise (Type_error(p,msg))

let subtype : term -> kind -> kind -> unit = fun t a b ->
  assert false

let rec type_check : term -> kind -> unit = fun t c ->
  match t.elt with
  | Coer(t,a) ->
      subtype t a c;
      type_check t a
  | TAbs(f) ->
      let a = new_uvar () in (* NOTE prefered name in uvar? *)
      type_check (subst f a) c
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
  | LLet(r,ps,f) -> (* FIXME *)
      let names = mbinder_names f in
      let arity = mbinder_arity f in
      let uvars = Array.init arity (fun _ -> new_uvar ()) in
      let cnsts = Array.mapi (fun i k -> cnst names.(i) k k) uvars in
      let terms = msubst f cnsts in
      for i = 0 to arity - 1 do
        type_check terms.(i+1) uvars.(i)
      done;
      type_check terms.(0) c
  | Reco(td,l,t) ->
      let a = new_uvar () in
      let b = new_uvar () in
      let c' = Prod(a,l,b) in
      subtype t c' c;
      type_check td a;
      type_check t b
  | URec -> ()
  | Proj(t,l) ->
      let c' = Prod(new_uvar (), l, c) in
      type_check t c'
  | VDef(v) ->
      begin
        match v.ttype with
        | Some a -> subtype v.value a c
        | None   -> type_check v.value c
      end
  | Prnt(_,t) ->
      type_check t c
  | Cnst(cst) ->
      let (_,a,_) = cst in
      subtype t a c
