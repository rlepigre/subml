open Bindlib
open Util
open Ast

let rec eval : term -> term = fun t0 ->
  match t0.elt with
  | Coer(t,_) -> eval t
  | LVar(_)   -> t0
  | LAbs(_,_) -> t0
  | KAbs(f) -> eval (subst f (Prod []))
  | Appl(t,u) ->
      begin
        let u' = eval u in
        let rec fn t =
	  let t' = eval t in
	  match t'.elt with
          | LAbs(_,b) -> eval (subst b u')
          | FixY(_,f) -> fn (subst f t')
          | t         -> dummy_pos (Appl(t',u'))
	in fn t
      end
  | Reco(l)   -> in_pos t0.pos (Reco (List.map (fun (s,t) -> (s, eval t)) l))
  | Proj(t,l) ->
      begin
        let t' = eval t in
        match t'.elt with
        | Reco(fs) ->
            begin
              try eval (List.assoc l fs)
              with Not_found -> dummy_pos (Proj(t',l))
            end
        | t        -> dummy_pos (Proj(t',l))
      end
  | Cons(s,t) -> in_pos t0.pos (Cons(s, eval t))
  | Case(t,l) ->
      begin
        let t' = eval t in
        match t'.elt with
        | Cons(c,v) ->
            begin
              try eval (dummy_pos (Appl(List.assoc c l, v)))
              with Not_found -> dummy_pos (Case(t',l))
            end
        | t   -> dummy_pos (Case(t',l))
      end
  | VDef(v)   -> eval v.value
  | Prnt(s)   -> Printf.printf "%s%!" s; in_pos t0.pos (Reco[])
  | FixY(_)   -> t0
  | Cnst(_)   -> invalid_arg "Constant during evaluation."
  | TagI(_)   -> invalid_arg "Integer tag during evaluation."
