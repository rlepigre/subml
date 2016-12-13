(****************************************************************************)
(**{3             Parser level AST and translation to final AST            }*)
(****************************************************************************)
open Ast
open Bindlib
open Position
open Binding
open LibTools

type pordinal = pordinal' position
and pordinal' =
  | PConv
  | PSucc of pordinal
  | PVari of string

type pkind = pkind' position
and pkind' =
  | PTVar of string * pordinal list * pkind list
  | PFunc of pkind * pkind
  | PProd of (string * pkind) list
  | PDSum of (string * pkind option) list
  | PKAll of string * pkind
  | PKExi of string * pkind
  | POAll of string * pkind
  | POExi of string * pkind
  | PFixM of pordinal * string * pkind
  | PFixN of pordinal * string * pkind
  | PWith of pkind * string * pkind
  | PUCst of pterm * string * pkind
  | PECst of pterm * string * pkind

and pterm  = pterm' position
and pterm' =
  | PCoer of pterm * pkind
  | PMLet of string list * string list * pkind * string * pterm
  | PLVar of string
  | PLAbs of (strpos * pkind option) list * pterm
  | PAppl of pterm * pterm
  | PReco of (string * pterm) list
  | PProj of pterm * string
  | PCons of string * pterm option
  | PCase of pterm * (string * ppat * pterm) list * (ppat * pterm) option
  | PPrnt of string
  | PFixY of strpos * bool * int * pterm
and ppat =
  | Simple of (strpos * pkind option) option
  | Record of (string * (strpos * pkind option)) list

let list_nil _loc =
  in_pos _loc (PCons("Nil" , None))

let list_cons _loc t l =
  let c = in_pos _loc (PReco [("hd",t);("tl",l)]) in
  in_pos _loc (PCons("Cons", Some c))

let dummy_case_var _loc =
  (in_pos _loc "_", Some(dummy_pos (PProd [])))

(* "t; u" := "(fun (_ : unit) ↦ u) t" *)
let sequence _loc t u =
  let dum = (in_pos _loc "_", Some(in_pos _loc (PProd []))) in
  in_pos _loc (PAppl(in_pos _loc (PLAbs([dum],u)), t))

let pfixY (id, ko) _loc n t =
  let n = match n with
    | None -> !(Typing.fixpoint_depth)
    | Some n -> n
  in
  match ko with
  | None   -> in_pos _loc (PFixY(id, n >= 0, abs n, t))
  | Some k -> in_pos _loc (PCoer(in_pos _loc (PFixY(id, n >= 0, abs n, t)), k))

let rec padd _loc o n =
  if n <= 0 then o else in_pos _loc (PSucc(padd _loc o (n-1)))

let pappl _loc t u = match t.elt with
  | PCons(t, None) -> in_pos _loc (PCons(t, Some u))
  | _ -> in_pos _loc (PAppl(t,u))

let apply_rpat x t =
  match x with
  | Simple x ->
     let x = from_opt x (dummy_case_var t.pos) in
     in_pos t.pos (PLAbs([x],t))
  | Record r ->
     let name = "@x" in
     let v = in_pos t.pos (PLVar name) in
     let t =
       List.fold_left (fun acc (l,x) ->
         (in_pos t.pos (PAppl(in_pos t.pos (PLAbs([x],acc)),
                              in_pos t.pos (PProj(v, l)))))) t r
     in
     in_pos t.pos (PLAbs([in_pos t.pos name, None],t))

let pcond _loc c t e =
  let l = [("Tru", Simple None, t); ("Fls", Simple None, e)] in
  in_pos _loc (PCase(c, l, None))

(****************************************************************************
 *                         Environment management                           *
 ****************************************************************************)

type env =
  { terms    : (string * tvar) list
  ; kinds    : (string * (kbox * occur)) list
  ; ordinals : (string * (obox * occur)) list }

let empty_env : env = { terms = [] ; kinds = [] ; ordinals = [] }

let add_term : string -> tvar -> env -> env = fun x t env ->
  { env with terms = (x,t) :: env.terms }

let add_kind : string -> kvar -> occur -> env -> env = fun x k occ env ->
  { env with kinds = (x,(box_of_var k,occ)) :: env.kinds }

let add_ordi : string -> ovar -> occur -> env -> env = fun x o occ env ->
  { env with ordinals = (x,(box_of_var o,occ)) :: env.ordinals }

let add_kinds : string array -> kvar array -> env -> env = fun ksn ks env ->
  let fn (i,env) x =  (i+1, add_kind ksn.(i) x Non env) in
  snd (Array.fold_left fn (0,env) ks)

let add_ordis : string array -> ovar array -> env -> env = fun osn os env ->
  let fn (i,env) x =  (i+1, add_ordi osn.(i) x Non env) in
  snd (Array.fold_left fn (0,env) os)


exception Unbound of strpos
let unbound s = raise (Unbound(s))

exception Arity_error of pos * string
let arity_error loc s = raise (Arity_error (loc,s))

exception Positivity_error of pos * string
let positivity_error loc s = raise (Positivity_error (loc,s))

(* Lookup a term variable in the environment. If it does not appear, look for
   the name in the list of term definitions. *)
let term_variable : env -> strpos -> tbox = fun env s ->
  try tvari s.pos (List.assoc s.elt env.terms) with Not_found ->
  try
    let vd = Hashtbl.find val_env s.elt in
    tdefi s.pos vd
  with Not_found -> unbound s

(* Lookup an ordinal variable in the environment. *)
let ordinal_variable : occur -> env -> strpos -> obox = fun pos env s ->
  try
    let (o, pos') = List.assoc s.elt env.ordinals in
    let _ = compose2 pos' pos in
    o
  with Not_found -> unbound s

(* TODO: the function below are certainly missing cases.
   this is only a syntactic sugar and we will discover it on examples *)
let rec with_clause a s b = match full_repr a with
  | KKExi(f) ->
     if binder_name f = s then subst f b else begin
       KKExi(binder_from_fun (binder_name f) (fun x ->
         with_clause (subst f x) s b))
     end
  | KFixM(OConv,f) -> with_clause (subst f (KFixM(OConv,f))) s b
  | KFixN(OConv,f) -> with_clause (subst f (KFixN(OConv,f))) s b
  | k       ->
     Io.log "KWith constraint on %s in %a\n%!" s (!fprint_kind false) k;
     failwith ("Illegal use of \"with\" on variable "^s^".")

(* Lookup a kind variable in the environment. If it does not appear, look for
   the name in the list of type definitions. *)
let rec kind_variable : occur -> env -> strpos -> pordinal array -> pkind array -> kbox =
 fun pos env s os ks ->
  let karity = Array.length ks in
  let oarity = Array.length os in
  try
    let (k, pos') = List.assoc s.elt env.kinds in
    if not (List.mem (compose2 pos' pos) [Non; Pos]) then
      let msg = Printf.sprintf "%s used in a negative position." s.elt in
      positivity_error s.pos msg
    else if oarity <> 0 then
      arity_error s.pos (s.elt ^ " does not expect ordinal arguments.")
    else if karity <> 0 then
      arity_error s.pos (s.elt ^ " does not expect kind arguments.")
    else k
  with Not_found ->
    try
      let td = Hashtbl.find typ_env s.elt in
      if td.tdef_oarity <> oarity then
        let msg =
          Printf.sprintf "%s expect %i ordinal arguments but received %i."
            s.elt td.tdef_oarity oarity
        in arity_error s.pos msg
      else if td.tdef_karity <> karity then
        let msg =
          Printf.sprintf "%s expect %i kind arguments but received %i."
            s.elt td.tdef_karity karity
        in arity_error s.pos msg
      else
      let os = Array.mapi (fun i o ->
        unsugar_ordinal ~pos:(compose2 (td.tdef_ovariance.(i)) pos) env o) os in
      let ks = Array.mapi (fun i k ->
        unsugar_kind ~pos:(compose2 (td.tdef_kvariance.(i)) pos) env k) ks
      in
      kdefi td os ks
    with Not_found -> unbound s

(****************************************************************************
 *                           Desugaring functions                           *
 ****************************************************************************)

and unsugar_ordinal : ?pos:occur -> env -> pordinal -> obox = fun ?(pos=Pos) env po ->
  match po.elt with
  | PConv   -> oconv
  | PVari s -> ordinal_variable pos env (in_pos po.pos s)
  | PSucc o -> osucc (unsugar_ordinal ~pos env o)

and unsugar_kind : ?pos:occur -> env -> pkind -> kbox =
  fun ?(pos=Pos) (env:env) pk ->
  match pk.elt with
  | PFunc(a,b)   ->
     kfunc (unsugar_kind ~pos:(neg pos) env a) (unsugar_kind ~pos env b)
  | PTVar(s,os,ks) ->
     kind_variable pos env (in_pos pk.pos s) (Array.of_list os) (Array.of_list ks)
  | PKAll(x,k)   -> let f xk =
                      unsugar_kind ~pos (add_kind x xk Non env) k
                    in kkall x f
  | PKExi(x,k)   -> let f xk =
                      unsugar_kind (add_kind x xk Non env) k
                    in kkexi x f
  | POAll(o,k)   -> let f xo =
                      unsugar_kind (add_ordi o xo Non env) k
                    in koall o f
  | POExi(o,k)   -> let f xo =
                      unsugar_kind (add_ordi o xo Non env) k
                    in koexi o f
  | PFixM(o,x,k) -> let o = unsugar_ordinal ~pos env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x xk pos env) k
                    in kfixm x o f
  | PFixN(o,x,k) -> let o = unsugar_ordinal ~pos:(neg pos) env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x xk pos env) k
                    in kfixn x o f
  | PProd(fs)    -> let f (l,k) = (l, unsugar_kind ~pos env k) in
                    kprod (List.map f fs)
  | PDSum(cs)    -> let f (c,ko) =
                      match ko with
                      | None   -> (c, kprod [])
                      | Some k -> (c, unsugar_kind ~pos env k)
                    in kdsum (List.map f cs)
  | PWith(a,s,b) -> lift_kind (with_clause (unbox (unsugar_kind ~pos env a))
                                 s (unbox (unsugar_kind ~pos env b)))
  | PUCst(t,x,k) -> let f xk = unsugar_kind ~pos:All (add_kind x xk Non env) k in
                    kucst x (unsugar_term env t) f
  | PECst(t,x,k) -> let f xk = unsugar_kind ~pos:All (add_kind x xk Non env) k in
                    kecst x (unsugar_term env t) f

and unsugar_term : env -> pterm -> tbox = fun env pt ->
  match pt.elt with
  | PLAbs(vs,t) -> let rec aux first env = function
                     | []           -> unsugar_term env t
                     | (x,ko) :: xs ->
                         let ko = map_opt (unsugar_kind env) ko in
                         let f xt = aux false (add_term x.elt xt env) xs in
                         let pos =
                           if first then pt.pos else
                           let open Position in
                           { pt.pos with line_start = x.pos.line_start
                           ; col_start = x.pos.col_start }
                         in
                         tabst pos ko x f
                   in aux true env vs
  | PCoer(t,k)  -> tcoer pt.pos (unsugar_term env t) (unsugar_kind env k)
  | PMLet(osn,ksn,k,x,t) ->
     let osn = Array.of_list osn and ksn = Array.of_list ksn in
     let mkenv os ks = add_ordis osn os (add_kinds ksn ks env) in
     let bk os ks = unsugar_kind (mkenv os ks) k in
     let x = match x with "" -> None | x -> Some (term_variable env (in_pos pt.pos x)) in
     let bt os ks = unsugar_term (mkenv os ks) t in
     tmlet pt.pos osn ksn bk x bt
  | PAppl(t,u)  -> tappl pt.pos (unsugar_term env t) (unsugar_term env u)
  | PLVar(x)    -> term_variable env (in_pos pt.pos x)
  | PPrnt(s)    -> tprnt pt.pos s
  | PCons(c,uo) -> let u =
                     match uo with
                     | None   -> treco pt.pos []
                     | Some u -> unsugar_term env u
                   in tcons pt.pos c u
  | PProj(t,l)  -> tproj pt.pos (unsugar_term env t) l
  |PCase(t,cs,d)-> let f (c,x,t) = (c, unsugar_term env (apply_rpat x t)) in
                   let g (x,t) = unsugar_term env (apply_rpat x t) in
                   tcase pt.pos (unsugar_term env t) (List.map f cs) (map_opt g d)
  | PReco(fs)   -> let f (l,t) = (l, unsugar_term env t) in
                   treco pt.pos (List.map f fs)
  | PFixY(x,b,n,t)-> let f xt = unsugar_term (add_term x.elt xt env) t in
                   tfixy pt.pos b n x f
