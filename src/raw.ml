(****************************************************************************)
(**{3             Parser level AST and translation to final AST            }*)
(****************************************************************************)

open LibTools
open Ast
open Bindlib
open Pos

type pordi = pordi' loc
and pordi' =
  | PConv
  | PSucc of pordi
  | PVari of string
  | POVar

type pkind = pkind' loc
and pkind' =
  | PTVar of string * pordi list * pkind list
  | PFunc of pkind * pkind
  | PProd of (string * pkind) list * bool
  | PDSum of (string * pkind option) list
  | PKAll of string list * pkind
  | PKExi of string list * pkind
  | POAll of string list * pkind
  | POExi of string list * pkind
  | PFixM of pordi * string * pkind
  | PFixN of pordi * string * pkind
  | PWith of pkind * string * pkind
  | PDPrj of strloc * string
  | PUCst of pterm * string * pkind
  | PECst of pterm * string * pkind
  | PUVar

and pterm  = pterm' loc
and pterm' =
  | PCoer of pterm * pkind
  | PMLet of string list * string list * pkind * string * pterm
  | PLVar of string
  | PLAbs of (strloc * pkind option) * pterm * sugar
  | PAppl of pterm * pterm
  | PReco of (string * pterm) list
  | PProj of pterm * string
  | PCons of string * pterm option
  | PCase of pterm * (string * ppat * pterm) list * (ppat * pterm) option
  | PPrnt of string
  | PFixY of strloc * int * pterm
  | PAbrt
and ppat =
  | NilPat
  | Simple of (strloc * pkind option) option
  | Record of (string * (strloc * pkind option)) list

let list_nil _loc =
  in_pos _loc (PCons("Nil" , None))

let list_cons _loc t l =
  let c = in_pos _loc (PReco [("hd",t);("tl",l)]) in
  in_pos _loc (PCons("Cons", Some c))

let unit_var _loc =
  (Pos.make _loc "", Some(Pos.none (PProd([],false))))

(* "t; u" := "(fun (_ : unit) ↦ u) t" *)
let sequence _loc t u =
  let dum = (in_pos _loc "_", Some(in_pos _loc (PProd([], false)))) in
  (* TODO: a desugaring info for printing could be used here *)
  in_pos _loc (PAppl(in_pos _loc (PLAbs(dum,u,SgNop)), t))

let fixpoint_depth = ref 3

let pfixY (id, ko) _loc n t =
  let n = match n with
    | None -> !fixpoint_depth
    | Some n -> n
  in
  match ko with
  | None   -> in_pos _loc (PFixY(id, abs n, t))
  | Some k -> in_pos _loc (PCoer(in_pos _loc (PFixY(id, abs n, t)), k))

let pcoer _loc t ko =
  match ko with
  | None   -> t
  | Some k -> in_pos _loc (PCoer(t,k))

let rec padd _loc o n =
  if n <= 0 then o else in_pos _loc (PSucc(padd _loc o (n-1)))

let pappl _loc t u = match t.elt with
  | PCons(t, None) -> in_pos _loc (PCons(t, Some u))
  | _ -> in_pos _loc (PAppl(t,u))

let apply_rpat c x t =
  match x with
  | NilPat ->
     Pos.make t.pos (PLAbs(unit_var t.pos,t,SgNil))
  | Simple x ->
     let x = Option.value x ~default:(unit_var t.pos) in
     Pos.make t.pos (PLAbs(x,t,SgNop))
  | Record r ->
     let is_cons =
       c = "Cons" && List.length r = 2 && List.mem_assoc "hd" r && List.mem_assoc "tl" r
     in
     let name, sugar =
       if is_cons then "@c", SgCns
       else if Print.is_tuple r then "@t", SgTpl (List.length r)
       else "@r", SgRec (List.map fst r)
     in
     let v = Pos.make t.pos (PLVar name) in
     let t =
       List.fold_left (fun acc (l,x) ->
         (Pos.make t.pos (PAppl(Pos.make t.pos (PLAbs(x,acc,SgNop)),
                              Pos.make t.pos (PProj(v, l)))))) t r
     in
     Pos.make t.pos (PLAbs((Pos.make t.pos name, None),t,sugar))

let rec plabs _loc rpats t =
  match rpats with
  | [] -> t
  | pat::rpats -> in_pos _loc (apply_rpat "_" pat (plabs _loc rpats t)).elt

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
  { env with kinds = (x, (box_var k, occ)) :: env.kinds }

let add_ordi : string -> ovar -> occur -> env -> env = fun x o occ env ->
  { env with ordinals = (x, (box_var o, occ)) :: env.ordinals }

let add_kinds : string array -> kvar array -> env -> env = fun ksn ks env ->
  let fn (i,env) x =  (i+1, add_kind ksn.(i) x Non env) in
  snd (Array.fold_left fn (0,env) ks)

let add_ordis : string array -> ovar array -> env -> env = fun osn os env ->
  let fn (i,env) x =  (i+1, add_ordi osn.(i) x Non env) in
  snd (Array.fold_left fn (0,env) os)


exception Unbound of string * popt
let unbound {elt;pos} = raise (Unbound(elt, pos))

exception Arity_error of popt * string
let arity_error : popt -> string -> 'a =
  fun loc s -> raise (Arity_error (loc,s))

exception Positivity_error of popt * string
let positivity_error : popt -> string -> 'a =
  fun loc s -> raise (Positivity_error (loc,s))

(* Lookup a term variable in the environment. If it does not appear, look for
   the name in the list of term definitions. *)
let term_variable : env -> strloc -> tbox = fun env s ->
  try tvari s.pos (List.assoc s.elt env.terms) with Not_found ->
  try
    let vd = Hashtbl.find val_env s.elt in
    tdefi s.pos vd
  with Not_found -> unbound s

(* Lookup an ordinal variable in the environment. *)
let ordinal_variable : occur -> env -> strloc -> obox = fun pos env s ->
  try
    let (o, pos') = List.assoc s.elt env.ordinals in
    let _ = compose2 pos' pos in
    o
  with Not_found -> unbound s

(* Lookup a kind variable in the environment. If it does not appear, look for
   the name in the list of type definitions. *)
let rec kind_variable : occur -> env -> strloc -> pordi array -> pkind array -> kbox =
 fun pos env s os ks ->
  let karity = Array.length ks in
  let oarity = Array.length os in
  try
    let (k, pos') = List.assoc s.elt env.kinds in
    let _ = compose2 pos' pos in
    if oarity <> 0 then
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

and unsugar_ordinal : ?pos:occur -> env -> pordi -> obox = fun ?(pos=sPos) env po ->
  match po.elt with
  | PConv   -> oconv
  | PVari s -> ordinal_variable pos env (Pos.make po.pos s)
  | PSucc o -> osucc (unsugar_ordinal ~pos env o)
  | POVar   -> box (new_ouvar ())

and unsugar_kind : ?pos:occur -> env -> pkind -> kbox =
  fun ?(pos=sPos) (env:env) pk ->
  let binds fn add env xs k =
    let rec f env =
      function
      | []    -> unsugar_kind ~pos env k
      | x::xs ->
         let g xk =
           f (add x xk Non env) xs
         in
         fn x g
    in
    f env xs
  in
  match pk.elt with
  | PFunc(a,b)   ->
     kfunc (unsugar_kind ~pos:(neg pos) env a) (unsugar_kind ~pos env b)
  | PTVar(s,os,ks) ->
     kind_variable pos env (Pos.make pk.pos s)
       (Array.of_list os) (Array.of_list ks)
  | PKAll(xs,k)  -> binds kkall add_kind env xs k
  | PKExi(xs,k)  -> binds kkexi add_kind env xs k
  | POAll(os,k)  -> binds koall add_ordi env os k
  | POExi(os,k)  -> binds koexi add_ordi env os k
  | PFixM(o,x,k) -> let o = unsugar_ordinal ~pos env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x xk pos env) k
                    in kfixm x o f
  | PFixN(o,x,k) -> let o = unsugar_ordinal ~pos:(neg pos) env o in
                    let f xk =
                      unsugar_kind ~pos (add_kind x xk pos env) k
                    in kfixn x o f
  | PProd(fs,e)  -> let f (l,k) = (l, unsugar_kind ~pos env k) in
                    kprod e (List.map f fs)
  | PDSum(cs)    -> let f (c,ko) =
                      match ko with
                      | None   -> (c, box kunit)
                      | Some k -> (c, unsugar_kind ~pos env k)
                    in kdsum (List.map f cs)
  | PWith(a,s,b) -> with_clause (unsugar_kind ~pos env a)
                              s (unsugar_kind ~pos env b)
  | PDPrj(x,s)   -> dot_proj (term_variable env x) s
  | PUCst(t,x,k) -> let f xk = unsugar_kind ~pos:All (add_kind x xk Non env) k in
                    kucst x (unsugar_term env t) f
  | PECst(t,x,k) -> let f xk = unsugar_kind ~pos:All (add_kind x xk Non env) k in
                    kecst x (unsugar_term env t) f
  | PUVar        -> box (new_kuvar ())

and unsugar_term : env -> pterm -> tbox = fun env pt ->
  match pt.elt with
  | PLAbs((x,ko),t,s) ->
     let ko = Option.map (unsugar_kind env) ko in
     let f xt = unsugar_term (add_term x.elt xt env) t in
     let pos = t.pos (* FIXME { t.pos with start_line = x.pos.start_line
                          ; start_col  = x.pos.start_col } *)
     in
     tabst pos ko x s f
  | PCoer(t,k)  -> tcoer pt.pos (unsugar_term env t) (unsugar_kind env k)
  | PMLet(osn,ksn,k,x,t) ->
     let osn = Array.of_list osn and ksn = Array.of_list ksn in
     let mkenv os ks = add_ordis osn os (add_kinds ksn ks env) in
     let bk os ks = unsugar_kind (mkenv os ks) k in
     let x =
       match x with
       | "" -> None
       | x  -> Some (term_variable env (Pos.make pt.pos x))
     in
     let bt os ks = unsugar_term (mkenv os ks) t in
     tmlet pt.pos osn ksn bk x bt
  | PAppl(t,u)  -> tappl pt.pos (unsugar_term env t) (unsugar_term env u)
  | PLVar(x)    -> term_variable env (Pos.make pt.pos x)
  | PPrnt(s)    -> tprnt pt.pos s
  | PCons(c,uo) -> let u =
                     match uo with
                     | None   -> treco pt.pos []
                     | Some u -> unsugar_term env u
                   in tcons pt.pos c u
  | PProj(t,l)  -> tproj pt.pos (unsugar_term env t) l
  |PCase(t,cs,d)-> let f (c,x,t) = (c, unsugar_term env (apply_rpat c x t)) in
                   let g (x,t) = unsugar_term env (apply_rpat "_" x t) in
                   tcase pt.pos (unsugar_term env t) (List.map f cs) (Option.map g d)
  | PReco(fs)   -> let f (l,t) = (l, unsugar_term env t) in
                   treco pt.pos (List.map f fs)
  | PFixY(x,n,t)-> let f xt = unsugar_term (add_term x.elt xt env) t in
                   tfixy pt.pos n x f
  | PAbrt       -> tabrt pt.pos
