(*****************************************************************************)
(**{3                       Call by value evaluation                        }*)
(*****************************************************************************)

open LibTools
open Pos
open Bindlib
open Ast

(* Call-by-value function. Raises the exception Assert_failure on runtime
   error, but this should never happen... *)
let rec eval : term -> term = fun t0 ->
  match t0.elt with
  (* Type annotations are ignored. *)
  | TCoer(t,_)   -> eval t
  | TMLet(_,_,bt)-> eval (mmsubst_dummy bt odummy kdummy)
  (* Unfold definition. *)
  | TDefi(v)     -> eval v.value
  (* A value has been reached. *)
  | TVari(_)     -> t0
  | TAbst _      -> t0
  | TFixY(_)     -> t0
  | TAbrt        -> t0
  (* Evaluate under products and constructors. *)
  | TReco(l)     -> Pos.make t0.pos (TReco(map_snd eval l))
  | TCons(c,t)   -> Pos.make t0.pos (TCons(c, eval t))
  (* Print instruction. *)
  | TPrnt(s)     -> Io.out "%s%!" s; Pos.make t0.pos (TReco([]))
  (* Constructors that should never appear in evaluation. *)
  | TCnst(_)     -> assert false
  (* Call-by-value application (λ-abstraction and fixpoint). *)
  | TAppl(t,u)   ->
      begin
        let u = eval u in
        let rec fn t =
          let t = eval t in
          match t.elt with
          | TAbst(_,b,_) -> eval (subst b u.elt)
          | TFixY(_,_,f) -> fn (subst f t.elt)
          | _            -> assert false
        in fn t
      end
  (* Record projection. *)
  | TProj(t,l)   ->
      begin
        let t = eval t in
        match t.elt with
        | TReco(fs) ->
            begin
              try List.assoc l fs (* Fields already evaluated. *)
              with Not_found -> assert false
            end
        | _         -> assert false
      end
  (* Case analysis. *)
  | TCase(t,l,d) ->
      begin
        let t = eval t in
        match t.elt with
        | TCons(c,v) ->
            begin
              try eval (Pos.none (TAppl(List.assoc c l, v)))
              with Not_found ->
                match d with
                | None   -> assert false
                | Some d -> eval (Pos.none (TAppl(d,t)))
            end
        | _          -> assert false
      end
  | TVars _ -> assert false
