(****************************************************************************)
(**{3                           You guessed it                             }*)
(****************************************************************************)

open Earley_core
open LibTools
open Earley
open Bindlib
open Ast
open Pos
open Print
open Eval
open TypingBase
open Typing
open Raw
open Format

(* Definition of a "location" function for DeCaP. *)
#define LOCATE locate

(****************************************************************************
 *                      Handling of blanks and comments                     *
 ****************************************************************************)

(* Exception raised when EOF is reached while parsing a comment. The boolean
   is set to true when EOF is reached while parsing a string. *)
exception Unclosed of bool * popt
let unclosed_comment in_string (buf,pos) =
  let p = Pos.locate buf pos buf (pos + if in_string then 1 else 2) in
  raise (Unclosed (in_string, Some p))

(* Blank function for basic blank characters (' ', '\t', '\r' and '\n') and
   comments delimited with "(*" and "*)". Nested comments (i.e. comments in
   comments) are supported. Arbitrary string litterals are also allowed in
   comments (including those containing comment closing sequences). *)
let subml_blank buf pos =
  let rec fn state stack prev curr =
    let (buf, pos) = curr in
    let (c, buf', pos') = Input.read buf pos in
    let next = (buf', pos') in
    match (state, stack, c) with
    (* Basic blancs. *)
    | (`Ini   , []  , ' '   )
    | (`Ini   , []  , '\t'  )
    | (`Ini   , []  , '\r'  )
    | (`Ini   , []  , '\n'  ) -> fn `Ini stack curr next
    (* Comment opening. *)
    | (`Ini   , _   , '('   ) -> fn (`Opn(curr)) stack curr next
    | (`Ini   , []  , _     ) -> curr
    | (`Opn(p), _   , '*'   ) -> fn `Ini (p::stack) curr next
    | (`Opn(_), _::_, '"'   ) -> fn (`Str(curr)) stack curr next (*#*)
    | (`Opn(_), []  , _     ) -> prev
    | (`Opn(_), _   , _     ) -> fn `Ini stack curr next
    (* String litteral in a comment (including the # rules). *)
    | (`Ini   , _::_, '"'   ) -> fn (`Str(curr)) stack curr next
    | (`Str(_), _::_, '"'   ) -> fn `Ini stack curr next
    | (`Str(p), _::_, '\\'  ) -> fn (`Esc(p)) stack curr next
    | (`Esc(p), _::_, _     ) -> fn (`Str(p)) stack curr next
    | (`Str(p), _::_, '\255') -> unclosed_comment true p
    | (`Str(_), _::_, _     ) -> fn state stack curr next
    | (`Str(_), []  , _     ) -> assert false (* Impossible. *)
    | (`Esc(_), []  , _     ) -> assert false (* Impossible. *)
    (* Comment closing. *)
    | (`Ini   , _::_, '*'   ) -> fn `Cls stack curr next
    | (`Cls   , _::_, '*'   ) -> fn `Cls stack curr next
    | (`Cls   , _::s, ')'   ) -> fn `Ini s curr next
    | (`Cls   , _::_, _     ) -> fn `Ini stack curr next
    | (`Cls   , []  , _     ) -> assert false (* Impossible. *)
    (* Comment contents (excluding string litterals). *)
    | (`Ini   , p::_, '\255') -> unclosed_comment false p
    | (`Ini   , _::_, _     ) -> fn `Ini stack curr next
  in
  fn `Ini [] (buf, pos) (buf, pos)

(****************************************************************************
 *                             Keyword management                           *
 ****************************************************************************)

let keywords = Hashtbl.create 20

let is_keyword : string -> bool = Hashtbl.mem keywords

let check_not_keyword : string -> unit = fun s ->
  if is_keyword s then give_up ()

let new_keyword : string -> unit grammar = fun s ->
  let ls = String.length s in
  if ls < 1 then raise (Invalid_argument "invalid keyword");
  if is_keyword s then raise (Invalid_argument "keyword already defied");
  Hashtbl.add keywords s s;
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to ls - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then give_up ();
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> give_up ()
    | _                                           -> ((), !str, !pos)
  in
  black_box f (Charset.singleton s.[0]) false s

(****************************************************************************
 *                   Some combinators and atomic parsers                    *
 ****************************************************************************)

let glist_sep   elt sep = parser
  | EMPTY                   -> []
  | e:elt es:{_:sep e:elt}* -> e::es

let glist_sep'  elt sep = parser
  | e:elt es:{_:sep e:elt}* -> e::es

let glist_sep'' elt sep = parser
  | e:elt es:{_:sep e:elt}+ -> e::es

let list_sep   elt sep = glist_sep   elt (string sep ())
let list_sep'  elt sep = glist_sep'  elt (string sep ())
let list_sep'' elt sep = glist_sep'' elt (string sep ())

let str_lit =
  let normal = in_charset
    (List.fold_left Charset.del Charset.full ['\\'; '"'; '\r'])
  in
  let schar = parser
    | "\\\""   -> "\""
    | "\\\\"   -> "\\"
    | "\\n"    -> "\n"
    | "\\t"    -> "\t"
    | c:normal -> String.make 1 c
  in
  change_layout (parser "\"" cs:schar* "\"" -> String.concat "" cs) no_blank

let parser int_lit = i:{#[-]?[0-9]+#} -> int_of_string i.(0)

let parser lid = id:{#[_a-z0-9][_a-zA-Z0-9]*[']*#}[group.(0)] ->
  if id = "_" then give_up (); check_not_keyword id; id

let parser uid = id:{#[A-Z][_a-zA-Z0-9]*[']*#}[group.(0)] ->
  check_not_keyword id; id

let parser loptident = lid | "_" -> ""
let parser llid = id:lid -> in_pos _loc id

let parser greek =
  | {"α" | "<alpha>"} -> "α"
  | {"β" | "<beta>" } -> "β"
  | {"γ" | "<gamma>"} -> "γ"
  | {"δ" | "<delta>"} -> "δ"

let parser lgid = g:greek l:{#[_][0-9]+#}[group.(0)]?[""] -> g ^ l

let build_prod l = List.mapi (fun i x -> (string_of_int (i+1), x)) l

(****************************************************************************
 *                                Basic tokens                              *
 ****************************************************************************)

let case_kw = new_keyword "case"
let rec_kw  = new_keyword "rec"
let let_kw  = new_keyword "let"
let such_kw = new_keyword "such"
let that_kw = new_keyword "that"
let val_kw  = new_keyword "val"
let of_kw   = new_keyword "of"
let in_kw   = new_keyword "in"
let fix_kw  = new_keyword "fix"
let fun_kw  = new_keyword "fun"
let if_kw   = new_keyword "if"
let then_kw = new_keyword "then"
let else_kw = new_keyword "else"
let with_kw = new_keyword "with"
let type_kw = new_keyword "type"
let abrt_kw = new_keyword "abort"

let clear_kw   = new_keyword "clear"
let quit_kw    = new_keyword "quit"
let exit_kw    = new_keyword "exit"
let eval_kw    = new_keyword "eval"
let set_kw     = new_keyword "set"
let include_kw = new_keyword "include"
let check_kw   = new_keyword "check"
let latex_kw   = new_keyword "latex"
let graphml_kw = new_keyword "graphml"

let parser arrow  : unit grammar = "→" | "->"
let parser forall : unit grammar = "∀" | "/\\"
let parser exists : unit grammar = "∃" | "\\/"
let parser mu     : unit grammar = "μ" | "!" | "<mu>"
let parser nu     : unit grammar = "ν" | "?" | "<nu>"
let parser time   : unit grammar = "×" | "*"
let parser lambda : unit grammar = "λ" | "\\"
let parser dot    : unit grammar = "."
let parser comma  : unit grammar = ","
let parser subset : unit grammar = "⊆" | "<"
let parser infty  : unit grammar = "∞" | "<infty>"
let parser eps    : unit grammar = "ε" | "<eps>"
let parser kuvar  : unit grammar = "?"
let parser ouvar  : unit grammar = "¿"
let parser dots   : unit grammar = "…" | "..."

let parser mem    : bool grammar =
  | {"∈" | "<in>"   } -> true
  | {"∉" | "<notin>"} -> false

let parser is_rec =
  | EMPTY  -> false
  | rec_kw -> true

let parser enables =
  | "on"  -> true
  | "off" -> false

(****************************************************************************
 *                  Parsers for ordinals and kinds (types)                  *
 ****************************************************************************)

(* Entry point for ordinals. *)
let parser ordi =
  | infty?               -> in_pos _loc PConv
  | s:lgid               -> in_pos _loc (PVari s)
  | o:ordi '+' n:int_lit -> padd _loc o n
  | ouvar                -> in_pos _loc POVar

(* Entry point for kinds. *)
let parser kind : pkind grammar = (pkind `Fun)

and parser kind_atm = (pkind `Atm)
and parser kind_prd = (pkind `Prd)

and parser ext =
  | EMPTY    -> false
  | ';' dots -> true

and parser pkind (p : [`Atm | `Prd | `Fun]) =
  | a:kind_prd arrow b:kind     when p = `Fun -> in_pos _loc (PFunc(a,b))
  | id:uid (o,k):kind_args      when p = `Atm -> in_pos _loc (PTVar(id,o,k))
  | forall id:uid* "." a:kind   when p = `Fun -> in_pos _loc (PKAll(id,a))
  | exists id:uid* "." a:kind   when p = `Fun -> in_pos _loc (PKExi(id,a))
  | forall id:lgid* "." a:kind  when p = `Fun -> in_pos _loc (POAll(id,a))
  | exists id:lgid* "." a:kind  when p = `Fun -> in_pos _loc (POExi(id,a))
  | mu o:ordi id:uid "." a:kind when p = `Fun -> in_pos _loc (PFixM(o,id,a))
  | nu o:ordi id:uid "." a:kind when p = `Fun -> in_pos _loc (PFixN(o,id,a))
  | "{" fs:kind_reco e:ext"}"   when p = `Atm -> in_pos _loc (PProd(fs,e))
  | fs:kind_prod                when p = `Prd -> in_pos _loc (PProd(fs,false))
  | "[" fs:kind_dsum "]"        when p = `Atm -> in_pos _loc (PDSum(fs))
  | a:kind_atm (s,b):with_eq    when p = `Atm -> in_pos _loc (PWith(a,s,b))
  | id:llid '.' s:uid           when p = `Atm -> in_pos _loc (PDPrj(id,s))
  (* Parenthesis and coercions. *)
  | "(" kind ")"                when p = `Atm
  | kind_atm                    when p = `Prd
  | kind_prd                    when p = `Fun
  | eps w:epsilon               when p = `Atm -> in_pos _loc w
  | kuvar                       when p = `Atm -> in_pos _loc PUVar

and parser epsilon = id:uid '(' t:term m:mem a:kind ')' ->
  if m then PECst(t,id,a) else PUCst(t,id,a)

and parser kind_args =
  | EMPTY                           -> ([], [])
  | "(" ks:(list_sep' kind ",") ")" -> ([], ks)
  | "(" os:(list_sep' ordi ",") ks:{"," ks:(list_sep kind ",")}?[[]] ")"

and parser kind_prod = fs:(glist_sep'' kind_atm time) -> build_prod fs
and parser kind_dsum = (list_sep (parser uid a:{_:of_kw kind}?) "|")
and parser kind_reco = (list_sep (parser lid ":" kind) ";")
and parser with_eq   = _:with_kw s:uid "=" b:kind_atm

(****************************************************************************
 *                              Parsers for terms                           *
 ****************************************************************************)

(* Entry point for terms. *)
and parser term : pterm grammar = (pterm `Lam)

and parser tapp = (pterm `App)
and parser tseq = (pterm `Seq)
and parser tcol = (pterm `Col)
and parser tatm = (pterm `Atm)

and parser pterm (p : [`Lam | `Seq | `App | `Col | `Atm]) =
  | lambda xs:fpat+ dot t:term    when p = `Lam -> plabs _loc xs t
  | fun_kw xs:fpat+ arrow t:term  when p = `Lam -> plabs _loc xs t
  | t:tapp u:tcol                 when p = `App -> pappl _loc t u
  | t:tapp ";" u:tseq             when p = `Seq -> sequence _loc t u
  | "print(" - s:str_lit - ")"    when p = `Atm -> in_pos _loc (PPrnt(s))
  | c:uid                         when p = `Atm -> in_pos _loc (PCons(c,None))
  | t:tatm "." l:lid              when p = `Atm -> in_pos _loc (PProj(t,l))
  | case_kw t:term of_kw ps:pats d:default?
                                  when p = `Lam -> in_pos _loc (PCase(t,ps,d))
  | "{" fs:term_reco "}"          when p = `Atm -> in_pos _loc (PReco(fs))
  | "(" fs:term_prod ")"          when p = `Atm -> in_pos _loc (PReco(fs))
  | id:lid                        when p = `Atm -> in_pos _loc (PLVar(id))
  | fix_kw n:{'[' n:int_lit ']'}? x:var arrow u:term
                                  when p = `Lam -> pfixY x _loc_u n u
  | "[" term_list "]"             when p = `Atm
  | term_llet                     when p = `Lam
  | term_mlet                     when p = `Lam
  | term_cond                     when p = `Atm
  | t:tapp "::" u:tseq            when p = `Seq -> list_cons _loc t u

  | abrt_kw                       when p = `Atm -> in_pos _loc PAbrt
  (* Parenthesis and coercions. *)
  | "(" t:term ko:{":" kind}? ")" when p = `Atm -> pcoer _loc t ko
  | tapp when p = `Seq
  | tseq when p = `Lam
  | tatm when p = `Col
  | tcol when p = `App

and parser var =
  | id:loptident                    -> (in_pos _loc_id id, None)
  | "(" id:loptident ":" k:kind ")" -> (in_pos _loc_id id, Some k)

and parser let_var =
  | id:loptident            -> (in_pos _loc_id id, None)
  | id:loptident ":" k:kind -> (in_pos _loc_id id, Some k)

and parser term_llet =
  let_kw r:is_rec n:{'[' n:int_lit ']'}? pat:rpat "=" t:term in_kw u:term ->
    let t =
      if not r then
        match pat with
        | Simple (Some(_,Some k)) -> in_pos _loc_t (PCoer(t,k))
        | _                       -> t
      else
        match pat with
        | Simple (Some id) -> pfixY id _loc_t n t
        | _                -> give_up ()
    in
    in_pos _loc (PAppl(apply_rpat "_" pat u, t))

and parser ords_kinds =
  | EMPTY                  -> ([], [])
  | ks:(list_sep' uid ",") -> ([], ks)
  | os:(list_sep' lgid ",") ks:{"," (list_sep uid ",")}?[[]]

and parser term_mlet = let_kw (os,ks):ords_kinds
                  such_kw that_kw id:loptident ':' k:kind in_kw u:term ->
  in_pos _loc (PMLet(os,ks,k,id,u))

and parser term_cond = if_kw c:term then_kw t:term else_kw e:term$ ->
  pcond _loc c t e

and parser term_reco = (list_sep field ";") _:";"?
and parser term_prod = l:(glist_sep'' term comma) -> build_prod l

and parser field = l:lid k:{ ":" kind }? "=" t:tapp ->
  (l, match k with None -> t | Some k -> in_pos _loc (PCoer(t,k)))

and parser term_list =
  | EMPTY                  -> list_nil _loc
  | t:term "," l:term_list -> list_cons _loc t l

and parser pats = _:"|"? ps:(list_sep case "|")

and parser fpat =
  | x:let_var                          -> Simple (Some x)
  | "(" x:let_var ")"                  -> Simple (Some x)
  | "{" ls:(list_sep (parser l:lid "=" x:var) ";") "}" -> Record ls
  | "(" ls:(glist_sep'' var comma) ")" -> Record (build_prod ls)

and parser rpat =
  | EMPTY -> Simple None
  | fpat

and parser pattern =
  | c:uid x:rpat   -> (c,x)
  | "[" "]"        -> ("Nil", NilPat)
  | x:var"::"y:var -> ("Cons", Record [("hd",x) ; ("tl",y)])

and parser case = (c,x):pattern arrow t:term -> (c, x, t)

and parser default = '|' x:let_var arrow t:term -> (Simple (Some x), t)

(****************************************************************************
 *                                LaTeX parser                              *
 ****************************************************************************)

(* Single '#' character (not followed by another one). *)
let hash =
  let fn buf pos = let (c,_,_) = Input.read buf pos in ((), c <> '#') in
  let no_hash = test ~name:"no_hash" Charset.full fn in
  parser '#' no_hash

(* Sequence of characters excluding '}', '{', '@' and '#'. *)
let tex_simple = parser s:{#[^}{@#]+#} -> s.(0)

(* Simple LaTeX text (without specific annotations. *)
let parser tex_name = '{' l:tex_name_aux* '}' -> String.concat "" l
and parser tex_name_aux =
  | s:tex_simple            -> s
  | "{" l:tex_name_aux* "}" -> "{" ^ (String.concat "" l) ^ "}"

(* LaTeX text with annotations to generate proofs and stuff. *)
let parser tex_text = "{" l:latex_atom* "}" -> Latex.List l

and parser latex_atom =
  | hash "witnesses" "#"
      -> Latex.Witnesses
  | hash br:int_lit?[0] u:"!"? k:(change_layout kind subml_blank) "#"
      -> Latex.Kind (br, u <> None, k)
  | "@" br:int_lit?[0] u:"!"? t:(change_layout term subml_blank) "@"
      -> Latex.Term (br, u <> None, t)
  | t:tex_simple
      -> Latex.Text t
  | l:tex_text
      -> l
  | hash "check" (a,b):sub "#"
      -> Latex.SProof (a,b)
  | hash br:int_lit?[0] ":" id:lid "#"
      -> Latex.KindOf (br, in_pos _loc_id id)
  | hash br:int_lit?[0] "?" id:uid "#"
      -> Latex.KindDef (br, in_pos _loc_id id)
  | "##" br:int_lit?[0] id:lid "#"
      -> Latex.TProof(br, in_pos _loc_id id)
  | hash "!" id:lid "#"
      -> Latex.Sct(in_pos _loc_id id)
  | hash "?" id:lid "." name:lid i:{"." int_lit}?[0]
             ordname:{"~" lgid}?["α"]  "#"
      -> Latex.Sch(in_pos _loc_id id,in_pos _loc_name name,i,ordname)

and parser sub = (change_layout (parser a:kind _:subset b:kind) subml_blank)

(* Entry points. *)
let tex_name = change_layout tex_name no_blank
let tex_text = change_layout tex_text no_blank

(****************************************************************************
 *                                    Actions                               *
 ****************************************************************************)

(* Optional TeX name and ASCII name. *)
type name = string option * string

(* New type definition. *)
let new_type : name -> (string list * string list) -> pkind -> unit =
  fun (tex, name) (oargs, kargs) k ->
    let tdef_tex_name =
      match tex with
      | None   -> "\\mathrm{"^name^"}"
      | Some s -> s
    in
    let oarg_names = Array.of_list oargs in
    let karg_names = Array.of_list kargs in
    let tdef_oarity = Array.length oarg_names in
    let tdef_karity = Array.length karg_names in
    let tdef_ovariance = Array.make tdef_oarity Non in
    let tdef_kvariance = Array.make tdef_karity Non in

    let fn oargs =
      let gn kargs =
        let kinds = ref [] in
        let f i k =
          let v = (k, (Reg(i,tdef_kvariance))) in
          kinds := (karg_names.(i), v) :: !kinds
        in
        Array.iteri f kargs;
        let ordis = ref [] in
        let f i o =
          let v = (o, (Reg(i,tdef_ovariance))) in
          ordis := (oarg_names.(i), v) :: !ordis
        in
        Array.iteri f oargs;
        unsugar_kind {empty_env with kinds = !kinds ; ordinals = !ordis} k
      in
      mbind mk_free_k karg_names gn
    in
    let b = mbind mk_free_o oarg_names fn in

    let tdef_value = unbox b in
    let td =
      { tdef_name = name ; tdef_tex_name ; tdef_karity ; tdef_oarity
      ; tdef_value ; tdef_kvariance ; tdef_ovariance }
    in
    if !verbose then Io.out "%a\n%!" (print_kind_def false) td;
    Hashtbl.add typ_env name td

type flag = MustPass | MustFail | CanFail

exception OK

let check pos flag f a =
  let res =
    try f a with
    | Error.Error l as e ->
        begin
          match flag with
          | MustPass -> raise e
          | MustFail
          | CanFail  -> raise OK
        end
    | Loop_error p as e ->
        begin
          match flag with
          | MustPass -> raise e
          | MustFail
          | CanFail  -> raise OK
        end
    | Sys.Break as e -> raise e
    | e              ->
       Printexc.print_backtrace stderr;
       Io.err "UNCAUGHT EXCEPTION: %s\n%!" (Printexc.to_string e);
       exit 1
  in
  if flag = CanFail then
    Io.out "A NEW TEST PASSED at %a.\n%!" print_position pos;
  if flag = MustFail then (
    Io.err "A WRONG TEST PASSED at %a\n%!" print_position pos;
    exit 1;
  ); res

(* New value definition. *)
let new_val : flag -> name -> pkind option -> pterm -> unit = fun fg nm k t ->
  let (tex_name, name) = nm in
  let tex_name = from_opt tex_name ("\\mathrm{" ^ name ^ "}") in
  let t = unbox (unsugar_term empty_env t) in
  let k = map_opt (fun k -> unbox (unsugar_kind empty_env k)) k in
  try
    let (k, proof, calls_graph) = check t.pos fg (type_check t) k in
    if !verbose then Io.out "val %s : %a\n%!" name (print_kind false) k;
    Hashtbl.add val_env name
      { name ; tex_name ; value = eval t ; orig_value = t
      ; ttype = k ; proof ; calls_graph }
  with OK -> ()

(* Check a subtyping relation. *)
let check_sub : popt -> flag -> pkind -> pkind -> unit = fun pos flag a b ->
  let a = unbox (unsugar_kind empty_env a) in
  let b = unbox (unsugar_kind empty_env b) in
  (try ignore (check pos flag (subtype None a) b) with OK -> ());
  reset_epsilon_tbls ()

(* Evaluate a term. *)
let eval_term : pterm -> unit = fun t ->
  let t = unbox (unsugar_term empty_env t) in
  let (k,_,_) = type_check t None in
  let t = eval t in
  if !verbose then
    Io.out "%a : %a\n%!" (print_term true) t (print_kind false) k

(* Load a file. *)
let read_file : (string -> unit) ref = ref (fun _ -> assert false)
let include_file : string -> unit = fun fn ->
  let open Latex in
  let s_ignore_latex = !ignore_latex in ignore_latex := true;
  let s_verbose = !Ast.verbose in Ast.verbose := false;
  (* FIXME should we save something else ? *)
  try
    !read_file fn;
    ignore_latex := s_ignore_latex; Ast.verbose := s_verbose
  with e ->
    ignore_latex := s_ignore_latex; Ast.verbose := s_verbose;
    raise e


let output_graphml : strloc -> unit = fun id ->
  try
    let prf = (Hashtbl.find val_env id.elt).proof in
    Graph.output Io.(fmts.gml) prf
  with Not_found -> unbound id

(****************************************************************************
 *                            Parsing of commands                           *
 ****************************************************************************)

let parser flag =
  | EMPTY -> MustPass
  | '!'   -> MustFail
  | '?'   -> CanFail

type vset =
  | Verbose of bool
  | TeXFile of string
  | GmlFile of string
  | PrntLet of bool

let do_vset = function
  | Verbose b  -> verbose := b
  | TeXFile fn -> Io.set_tex_file fn
  | GmlFile fn -> Io.set_gml_file fn
  | PrntLet b  -> Print.print_redex_as_let := true

type command =
  | Type of string option * string * (string list * string list) * pkind
  | Defi of flag * (string option * string) * pkind option * pterm
  | Eval of pterm
  | Chck of pos * flag * pkind * pkind
  | Incl of string
  | GrMl of string loc
  | LaTX of Latex.latex_output
  | VSet of vset
  | Clr
  | Quit

let execute = function
  | Type(tn,n,args,k) -> new_type (tn,n) args k
  | Eval(t)           -> eval_term t
  | Defi(f,n,k,t)     -> new_val f n k t
  | Chck(pos,f,a,b)   -> check_sub (Some pos) f a b
  | Incl(fn)          -> include_file fn
  | GrMl(id)          -> output_graphml id
  | LaTX(t)           -> Io.tex "%a%!" Latex.output t
  | VSet(s)           -> do_vset s
  | Clr               -> LibTools.clear ()
  | Quit              -> raise End_of_file (* FIXME *)

let parser vset top =
  | "verbose" b:enables               -> Verbose(b)
  | "texfile" fn:str_lit when not top -> TeXFile(fn)
  | "gmlfile" fn:str_lit when not top -> GmlFile(fn)
  | "prntlet" b:enables               -> PrntLet(b)

let parser command top =
  | type_kw (tn,n,args,k):kind_def         -> Type(tn,n,args,k)
  | eval_kw t:term                         -> Eval(t)
  | f:flag val_kw (n,k,t):val_def          -> Defi(f, n, k, t)
  | f:flag check_kw a:kind _:subset b:kind -> Chck(_loc,f,a,b)
  | _:include_kw fn:str_lit                -> Incl(fn)
  | _:graphml_kw id:llid                   -> GrMl(id)
  | latex_kw t:tex_text when not top       -> LaTX(t)
  | set_kw s:(vset top)                    -> VSet(s)
  | _:clear_kw          when top           -> Clr
  | {quit_kw | exit_kw} when top           -> Quit


and parser kind_def = tex_name? uid kind_def_args "=" kind

and parser kind_def_args =
  | EMPTY                          -> ([], [])
  | "(" ks:(list_sep' uid ",") ")" -> ([], ks)
  | "(" os:(list_sep' lgid ",") ks:{"," (list_sep uid ",")}?[[]] ")"

and parser val_def =
  | r:is_rec n:{'[' int_lit ']'}? tex:tex_name? id:lid k:{":" kind}?
    "=" t:term ->
      let t =
        if not r then t else pfixY (in_pos _loc_id id, None) _loc_t n t
      in ((tex,id), k, t)

(****************************************************************************
 *                       High-level parsing functions                       *
 ****************************************************************************)

let toplevel_of_string : string -> command =
  parse_string (command true) subml_blank

let eval_string : string -> string -> unit = fun filename input ->
  let commands =
    parse_string ~filename (parser (command false)*) subml_blank input
  in
  List.iter execute commands

let eval_file =
  let eval_file fn =
    let buf = Io.file fn in
    if !verbose then Io.out "## loading file %S\n%!" fn;
    let commands = parse_buffer (parser (command false)*) subml_blank buf in
    List.iter execute commands
  in
  read_file := eval_file; eval_file

let handle_exception : ('a -> 'b) -> 'a -> bool = fun fn v ->
  let pp = print_position in
  let ok = ref false in
  begin
    try fn v; ok := true with
    | End_of_file            -> raise End_of_file
    | Sys.Break              -> Io.err "\n[Interrupted]\n%!"
    | Arity_error(p,m)       -> Io.err "%a: %s\n%!" pp p m
    | Positivity_error(p,m)  -> Io.err "%a: %s\n%!" pp p m
    | Parse_error(buf,pos)   -> Io.err "%a: syntax error.\n%!" pp
                                  (Some (Pos.locate buf pos buf (pos+1)))
    | Unclosed(b,p)          -> Io.err "%a: unclosed %scomment.\n%!" pp p
                                  (if b then "string in a " else "")
    | Unbound(s,p)           -> Io.err "%a: unbound variable %s.\n%!" pp p s
    | Error.Error l          -> Io.err "%a: error:\n%!" Error.display_errors l
    | Loop_error(p)          -> Io.err "%a: loops...\n%!" pp p
  end; !ok
