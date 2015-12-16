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
        let u' = eval st u in
        let t' = eval st t in
        match t'.elt with
        | LAbs(_,b) -> eval st (subst b u')
        | FixY(f)   -> eval st (dummy_pos (Appl(f, dummy_pos (Appl(t',u')))))
        | t         -> dummy_pos (Appl(t',u'))
      end
  | Reco(l)   -> in_pos t0.pos (Reco (List.map (fun (s,t) -> (s, eval st t)) l))
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
  | Cons(s,t) -> in_pos t0.pos (Cons(s, eval st t))
  | Case(t,l) ->
      begin
        let t' = eval st t in
        match t'.elt with
        | Cons(c,v) ->
            begin
              try eval st (subst (List.assoc c l) v)
              with Not_found -> dummy_pos (Case(t',l))
            end
        | t   -> dummy_pos (Case(t',l))
      end
  | VDef(v)   -> eval st v.value
  | Prnt(s)   -> Printf.printf "%s%!" s; in_pos t0.pos (Reco[])
  | FixY(_)   -> t0
  | Cnst(_)   -> invalid_arg "Constant during evaluation."
  | TagI(_)   -> invalid_arg "Integer tag during evaluation."
