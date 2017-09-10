(*****************************************************************************)
(**{3                       Call by value evaluation                        }*)
(*****************************************************************************)

open Pos
open Bindlib
open Ast
open LibTools

type stack =
  | Vide
  | Fram of (term -> stack -> term) * stack

(* Call-by-value function. Raises the exception Assert_failure on runtime
   error, but this should never happen... *)
let eval : term -> term =
  let unfold v stack =
    match stack with
    | Empty   -> v
    | Frame(f,s) -> f v s
  in
  let rec eval t0 stack = match t0.elt with
  (* Type annotations are ignored. *)
  | TCoer(t,_)   -> eval t stack
  | TMLet(b,x,bt)-> eval (mmsubst_dummy bt odummy kdummy) stack
  (* Unfold definition. *)
  | TDefi(v)     -> eval v.value stack
  (* A value has been reached. *)
  | TVari(_)     -> unfold t0 stack
  | TAbst(_,f,_) -> unfold t0 stack
  | TCaco        -> unfold t0 stack
  | TStck _      -> unfold t0 stack

  | TAbrt        -> t0
  | TFixY(_,_,f) -> eval (subst f t0.elt) stack

  (* Evaluate under products and constructors. *)
  | TReco(l)     ->
     let rec f acc l name v s = match l with
       | [] -> unfold (Pos.make t0.pos (TReco(List.rev ((name,v)::acc)))) s
       | (name', t)::l' ->
          eval t (Frame(f ((name,v)::acc) l' name', s))
     in
     begin
       match l with
       | [] -> unfold (Pos.make t0.pos (TReco [])) stack
       | (name,t)::l -> eval t (Frame(f [] l name, stack))
     end
  | TCons(c,t)   ->
     let f v s = unfold (Pos.make t0.pos (TCons(c,v))) s in
     eval t (Frame(f,stack))
  (* Print instruction. *)
  | TPrnt(s)     -> Io.out "%s%!" s; unfold (Pos.make t0.pos (TReco [])) stack
  (* Constructors that should never appear in evaluation. *)
  | TCnst(_)     -> assert false
  (* Call-by-value application (λ-abstraction and fixpoint). *)
  | TAppl(t,u)   ->
     let f v s =
       let g w s =
         match w.elt with
         | TAbst(_,b,_) -> eval (subst b v.elt) s
         | TCaco ->
            Printf.printf "save\n%!";
            eval (Pos.none (TAppl(v, Pos.none (TStck s)))) Empty
         | TStck s' -> Printf.printf "restore\n%!"; unfold v s'
         | _ -> assert false
       in
       eval t (Frame(g,s))
     in
     eval u (Frame(f,stack))
  (* Record projection. *)
  | TProj(t,l)   ->
     let f v s =
        match v.elt with
        | TReco(fs) ->
            begin
              try unfold (List.assoc l fs) s (* Fields already evaluated. *)
              with Not_found -> assert false
            end
        | _         -> assert false
     in
     eval t (Frame(f,stack))
  (* Case analysis. *)
  | TCase(t,l,d) ->
     let f v s =
        match v.elt with
        | TCons(c,v) ->
            begin
              try eval (Pos.none (TAppl(List.assoc c l, v))) s
              with Not_found ->
                match d with
                | None   -> assert false
                | Some d -> eval (Pos.none (TAppl(d,t))) s
            end
        | _          -> assert false
     in eval t (Frame(f,stack))
  | TVars _ -> assert false
  in
  fun t -> eval t Empty
