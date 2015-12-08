open Bindlib
open Util
open Ast

let rec eval : state -> term -> term = fun st t0 ->
  match t0.elt with
  | Coer(t,_) -> eval st t
  | LVar(_)   -> t0
  | LAbs(_,_) -> t0
  | Appl(t,u) ->
      begin
        let t' = eval st t in
        match t'.elt with
        | LAbs(_,b) -> eval st (subst b u)
        | FixY      -> eval st (dummy_pos (Appl(u, dummy_pos (Appl(t',u)))))
        | t         -> dummy_pos (Appl(t',u))
      end
  | Reco(_)   -> t0
  | Proj(t,l) ->
      begin
        let t' = eval st t in
        match t'.elt with
        | Reco(fs) ->
            begin
              try eval st (List.assoc l fs)
              with Not_found -> dummy_pos (Proj(t',l))
            end
        | t        -> dummy_pos (Proj(t',l))
      end
  | Cons(_,_) -> t0
  | Case(t,l) ->
      begin
        let t' = eval st t in
        match t'.elt with
        | Cons(c,v) ->
            begin
              try eval st (subst (List.assoc c l) v)
              with Not_found -> dummy_pos (Case(t',l))
            end
        | t         -> dummy_pos (Case(t',l))
      end
  | VDef(v)   -> eval st v.value
  | Prnt(s,t) -> Printf.printf "%s%!" s; eval st t
  | FixY      -> t0
  | Cnst(_)   -> invalid_arg "Constant during evaluation."
  | TagI(_)   -> invalid_arg "Integer tag during evaluation."
