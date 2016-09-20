open Decap
open Bindlib
open Ast
open Position
open Print
open Eval
open Typing
open Raw
open Format
open Position

(* Definition of a "location" function for DeCaP. *)
#define LOCATE locate

(****************************************************************************
 *                    Missing standard library functions                    *
 ****************************************************************************)

let int_of_chars s =
  let f acc c = acc * 10 + (Char.code c - Char.code '0') in
  List.fold_left f 0 (List.rev s)

let string_of_chars s =
  let s = Array.of_list s in
  let res = String.make (Array.length s) ' ' in
  Array.iteri (fun i c -> res.[i] <- c) s; res

(****************************************************************************
 *                      Handling of blanks and comments                     *
 ****************************************************************************)

(* Exception raised when EOF is reached while parsing a comment. The boolean
   is set to true when EOF is reached while parsing a string. *)
exception Unclosed_comment of bool * (string * int * int)

let unclosed_comment in_string (buf,pos) =
  let position = (Input.fname buf, Input.line_num buf, pos) in
  raise (Unclosed_comment (in_string, position))

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
  if is_keyword s then
    give_up ("\""^s^"\" is a reserved identifier...")

let new_keyword : string -> unit grammar = fun s ->
  let ls = String.length s in
  if ls < 1 then raise (Invalid_argument "invalid keyword");
  if is_keyword s then raise (Invalid_argument "keyword already defied");
  Hashtbl.add keywords s s;
  let fail () = give_up ("The keyword "^s^" was expected...") in
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to ls - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then fail ();
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> fail ()
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

let digit       = Charset.range '0' '9'
let lowercase   = Charset.range 'a' 'z'
let uppercase   = Charset.range 'A' 'Z'
let underscore  = Charset.singleton '_'
let letter      = Charset.union lowercase uppercase
let identany    = Charset.union letter (Charset.union digit underscore)
let lidentfirst = Charset.union lowercase (Charset.union digit underscore)

let string_lit =
  let normal = in_charset
    (List.fold_left Charset.del Charset.full_charset ['\\'; '"'; '\r'])
  in
  let schar = parser
    | "\\\""   -> "\""
    | "\\\\"   -> "\\"
    | "\\n"    -> "\n"
    | "\\t"    -> "\t"
    | c:normal -> String.make 1 c
  in
  change_layout (parser "\"" cs:schar* "\"" -> String.concat "" cs) no_blank

let int_lit = change_layout (
    parser s:(in_charset digit)+ -> int_of_chars s
  ) no_blank

let ident first =
  let first = in_charset first and any = in_charset identany in
  let lident = parser c:first s:any* ps:'\''* -> string_of_chars (c::s@ps) in
  let lident = change_layout lident no_blank in
  Decap.apply (fun id -> check_not_keyword id; id) lident

let parser lident = s:(ident lidentfirst) -> if s = "_" then give_up ""; s
let uident = ident uppercase
let parser loptident = lident | "_" -> ""

let parser lgident =
  | "α" -> "α"
  | "β" -> "α"
  | "γ" -> "γ"
  | "δ" -> "δ"
  | "ε" -> "ε"

let build_prod l = List.mapi (fun i x -> (string_of_int (i+1), x)) l

(****************************************************************************
 *                                Basic tokens                              *
 ****************************************************************************)

let case_kw = new_keyword "case"
let rec_kw  = new_keyword "rec"
let let_kw  = new_keyword "let"
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

let unfold_kw  = new_keyword "unfold"
let clear_kw   = new_keyword "clear"
let parse_kw   = new_keyword "parse"
let quit_kw    = new_keyword "quit"
let exit_kw    = new_keyword "exit"
let eval_kw    = new_keyword "eval"
let set_kw     = new_keyword "set"
let include_kw = new_keyword "include"
let check_kw   = new_keyword "check"
let latex_kw   = new_keyword "latex"
let html_kw    = new_keyword "html"

let parser arrow  : unit grammar = "→" | "->"
let parser forall : unit grammar = "∀" | "/\\"
let parser exists : unit grammar = "∃" | "\\/"
let parser mu     : unit grammar = "μ" | "!"
let parser nu     : unit grammar = "ν" | "?"
let parser time   : unit grammar = "×" | "*"
let parser lambda : unit grammar = "λ"
let parser klam   : unit grammar = "Λ" | "/\\"
let parser dot    : unit grammar = "."
let parser comma  : unit grammar = ","
let parser subset : unit grammar = "⊂" | "⊆" | "<"
let parser infty  : unit grammar = "∞"

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
let parser ordinal : pordinal Decap.grammar =
  | infty?                  -> in_pos _loc PConv
  | s:lgident               -> in_pos _loc (PVari s)
  | o:ordinal '+' n:int_lit -> padd _loc o n

(* Entry point for kinds. *)
let parser kind : pkind Decap.grammar = (pkind `Fun)

and kind_atm = (pkind `Atm)
and kind_prd = (pkind `Prd)

and pkind (p : [`Atm | `Prd | `Fun]) =
  | a:kind_prd arrow b:kind       when p = `Fun -> in_pos _loc (PFunc(a,b))
  | id:uident (o,k):kind_args$    when p = `Atm -> in_pos _loc (PTVar(id,o,k))
  | forall id:uident a:kind       when p = `Fun -> in_pos _loc (PKAll(id,a))
  | exists id:uident a:kind       when p = `Fun -> in_pos _loc (PKExi(id,a))
  | forall id:lgident a:kind      when p = `Fun -> in_pos _loc (POAll(id,a))
  | exists id:lgident a:kind      when p = `Fun -> in_pos _loc (POExi(id,a))
  | mu o:ordinal id:uident a:kind when p = `Fun -> in_pos _loc (PFixM(o,id,a))
  | nu o:ordinal id:uident a:kind when p = `Fun -> in_pos _loc (PFixN(o,id,a))
  | "{" fs:kind_reco "}"          when p = `Atm -> in_pos _loc (PProd(fs))
  | fs:kind_prod                  when p = `Prd -> in_pos _loc (PProd(fs))
  | "[" fs:kind_dsum "]"          when p = `Atm -> in_pos _loc (PDSum(fs))
  | t:tatm "." s:uident           when p = `Atm -> in_pos _loc (PDPrj(t,s))
  | a:kind_atm (s,b):with_eq      when p = `Atm -> in_pos _loc (PWith(a,s,b))
  (* Parenthesis and coercions. *)
  | "(" kind ")"                  when p = `Atm
  | kind_atm                      when p = `Prd
  | kind_prd                      when p = `Fun

and kind_args =
  | EMPTY                           -> ([], [])
  | "(" ks:(list_sep' kind ",") ")" -> ([], ks)
  | "(" os:(list_sep' ordinal ",") ks:{"," ks:(list_sep kind ",")}?[[]] ")"

and kind_prod = fs:(glist_sep'' kind_atm time) -> build_prod fs
and kind_dsum = (list_sep (parser uident a:{_:of_kw kind}?) "|")
and kind_reco = (list_sep (parser lident ":" kind) ";")
and with_eq   = _:with_kw s:uident "=" b:kind_atm

(****************************************************************************
 *                              Parsers for terms                           *
 ****************************************************************************)

(* Entry point for terms. *)
and term : pterm Decap.grammar = (pterm `Lam)

and tapp = (pterm `App)
and tseq = (pterm `Seq)
and tcol = (pterm `Col)
and tatm = (pterm `Atm)

and pterm (p : [`Lam | `Seq | `App | `Col | `Atm]) =
  | lambda xs:var+ dot t:term$    when p = `Lam -> in_pos _loc (PLAbs(xs,t))
  | fun_kw xs:var+ arrow t:term$  when p = `Lam -> in_pos _loc (PLAbs(xs,t))
  | klam x:uident t:term$         when p = `Lam -> let x = in_pos _loc_x x in
                                                   in_pos _loc (PKAbs(x,t))
  | klam o:lgident t:term$        when p = `Lam -> let o = in_pos _loc_o o in
                                                   in_pos _loc (POAbs(o,t))
  | t:tapp u:tcol                 when p = `App -> pappl _loc t u
  | t:tapp ";" u:tseq             when p = `Seq -> sequence _loc t u
  | "print(" - s:string_lit - ")" when p = `Atm -> in_pos _loc (PPrnt(s))
  | c:uident                      when p = `Atm -> in_pos _loc (PCons(c,None))
  | t:tatm "." l:lident           when p = `Atm -> in_pos _loc (PProj(t,l))
  | case_kw t:term of_kw ps:pats d:default? $
                                  when p = `Lam -> in_pos _loc (PCase(t,ps,d))
  | "{" fs:term_reco "}"          when p = `Atm -> in_pos _loc (PReco(fs))
  | "(" fs:term_prod ")"          when p = `Atm -> in_pos _loc (PReco(fs))
  | t:tcol ":" k:kind$            when p = `Col -> in_pos _loc (PCoer(t,k))
  | id:lident                     when p = `Atm -> in_pos _loc (PLVar(id))
  | fix_kw n:int_lit? x:var arrow u:term$
                                  when p = `Lam -> pfixY x _loc_u n u
  | "[" term_list "]"             when p = `Atm
  | term_llet                     when p = `Lam
  | term_cond                     when p = `Atm
  | t:tapp "::" u:tseq$           when p = `Seq -> list_cons _loc t u
  (* Parenthesis and coercions. *)
  | "(" term ")" when p = `Atm
  | tapp when p = `Seq
  | tseq when p = `Lam
  | tatm when p = `Col
  | tcol when p = `App

and var =
  | id:loptident                    -> (in_pos _loc_id id, None)
  | "(" id:loptident ":" k:kind ")" -> (in_pos _loc_id id, Some k)

and let_var =
  | id:loptident            -> (in_pos _loc_id id, None)
  | id:loptident ":" k:kind -> (in_pos _loc_id id, Some k)

and term_llet = let_kw r:is_rec n:int_lit? pat:rpat "=" t:term in_kw u:term ->
  let t =
    if not r then
      match pat with Simple (Some(_,Some k)) -> in_pos _loc_t (PCoer(t,k))
      | _ -> t
    else
      match pat with Simple (Some id) -> pfixY id _loc_t n t
      | _ -> give_up ""
  in
  in_pos _loc (PAppl(apply_rpat pat u, t))

and term_cond = if_kw c:term then_kw t:term else_kw e:term$ ->
  pcond _loc c t e

and term_reco = (list_sep field ";") _:";"?
and term_prod = l:(glist_sep'' term comma) -> build_prod l

and field = l:lident k:{ ":" kind }?$ "=" t:tapp$ ->
  (l, match k with None -> t | Some k -> in_pos _loc (PCoer(t,k)))

and term_list =
  | EMPTY                  -> list_nil _loc
  | t:term "," l:term_list -> list_cons _loc t l

and pats = _:"|"? ps:(list_sep case "|")

and rpat =
  | EMPTY                              -> Simple None
  | x:let_var                          -> Simple (Some x)
  | "(" x:let_var ")"                      -> Simple (Some x)
  | "{" ls:(list_sep (parser l:lident "=" x:var) ";") "}"
                                       -> Record ls
  | "(" ls:(glist_sep'' var comma) ")" -> Record (build_prod ls)

and pattern =
  | c:uident x:rpat -> (c,x)
  | "[" "]"         -> ("Nil", Simple None)
  | x:var"::"y:var  -> ("Cons", Record [("hd",x) ; ("tl",y)])

and case = (c,x):pattern arrow t:term -> (c, x, t)

and default = '|' x:let_var arrow t:term -> (Simple (Some x), t)

(****************************************************************************
 *                                LaTeX parser                              *
 ****************************************************************************)

(* Single '#' character (not followed by another one). *)
let hash =
  let fn buf pos = let (c,_,_) = Input.read buf pos in ((), c <> '#') in
  let no_hash = Decap.test ~name:"no_hash" Charset.full_charset fn in
  parser '#' no_hash

(* Sequence of characters excluding '}', '{', '@' and '#'. *)
let tex_simple =
  let cs = Charset.(List.fold_left del full_charset ['}';'{';'@';'#']) in
  parser cs:(Decap.change_layout (parser (in_charset cs)+) no_blank) ->
    string_of_chars cs

(* Simple LaTeX text (without specific annotations. *)
let parser tex_name = '{' l:tex_name_aux* '}' -> String.concat "" l
and tex_name_aux =
  | s:tex_simple            -> s
  | "{" l:tex_name_aux* "}" -> "{" ^ (String.concat "" l) ^ "}"

(* LaTeX text with annotations to generate proofs and stuff. *)
let parser tex_text = "{" l:latex_atom* "}" -> Latex.List l

and latex_atom =
  | hash "witnesses" "#" ->
      Latex.Witnesses
  | hash br:int_lit?[0] u:"!"? k:(change_layout kind subml_blank) "#" ->
      Latex.Kind (br, u <> None, unbox (unsugar_kind empty_env k))
  | "@" br:int_lit?[0] u:"!"? t:(change_layout term subml_blank) "@" ->
      Latex.Term (br, u <> None, unbox (unsugar_term empty_env t))
  | t:tex_simple$ ->
      Latex.Text t
  | tex_text
  | hash "check" (a,b):sub "#" ->
      let a = unbox (unsugar_kind empty_env a) in
      let b = unbox (unsugar_kind empty_env b) in
      let (prf, cg) = subtype a b in
      Latex.SProof (prf, cg)
  | hash br:int_lit?[0] ":" id:lident "#" ->
      Latex.Kind (br, false, (Hashtbl.find val_env id).ttype)
  | hash br:int_lit?[0] "?" id:uident "#" ->
      Latex.KindDef (br, Hashtbl.find typ_env id)
  | "##" id:lident "#" ->
      Latex.TProof (Hashtbl.find val_env id).proof
  | "#!" id:lident "#" ->
      Latex.Sct (Hashtbl.find val_env id).calls_graph

and sub = (change_layout (parser a:kind _:subset b:kind) subml_blank)

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
      mbind mk_free_kvari karg_names gn
    in
    let b = mbind mk_free_ovari oarg_names fn in

    let tdef_value = unbox b in
    let td =
      { tdef_name = name ; tdef_tex_name ; tdef_karity ; tdef_oarity
      ; tdef_value ; tdef_kvariance ; tdef_ovariance }
    in
    if !verbose then Io.out "%a\n%!" (print_kind_def false) td;
    Hashtbl.add typ_env name td

type flag = MustPass | MustFail | CanFail

(* New value definition. *)
let new_val : flag -> name -> pkind option -> pterm -> unit = fun f nm k t ->
  let (tex_name, name) = nm in
  let tex_name = from_opt tex_name ("\\mathrm{" ^ name ^ "}") in
  let t = unbox (unsugar_term empty_env t) in
  let k = map_opt (fun k -> unbox (unsugar_kind empty_env k)) k in
  (* TODO handle flag. *)
  let (k, proof, calls_graph) = type_check t k in
  if !verbose then Io.out "val %s : %a\n%!" name (print_kind false) k;
  Hashtbl.add val_env name
    { name ; tex_name ; value = eval t ; orig_value = t
    ; ttype = k ; proof ; calls_graph }

(* Check a subtyping relation. *)
let check_sub : flag -> pkind -> pkind -> unit = fun f a b ->
  let a = unbox (unsugar_kind empty_env a) in
  let b = unbox (unsugar_kind empty_env b) in
  begin
    try ignore (subtype a b) with
    | Error.Error l ->
        begin
          match f with
          | MustPass -> Io.err "CHECK FAILED: %a\n%!" Error.display_errors l; failwith "check"
          | MustFail -> ()
          | CanFail  -> ()
        end
    | Loop_error ->
        begin
          match f with
          | MustPass -> Io.err "CHECK FAILED: LOOP\n%!"; failwith "check"
          | MustFail -> ()
          | CanFail  -> ()
        end
    | e               ->
        Io.err "UNCAUGHT EXCEPTION: %s\n%!" (Printexc.to_string e);
        failwith "check"
  end;
  if f = CanFail then Io.out "A NEW TEST PASSED.\n%!";
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


let output_html : strpos -> unit = fun id ->
  try
    let prf = (Hashtbl.find val_env id.elt).proof in
    Graph.output_html Io.(fmts.htm) (Print.typ2proof prf)
  with Not_found -> unbound id

(****************************************************************************
 *                            Parsing of commands                           *
 ****************************************************************************)

let parser flag =
  | EMPTY -> MustPass
  | '!'   -> MustFail
  | '?'   -> CanFail

let parser command top =
  | type_kw (tn,n,args,k):kind_def$               -> new_type (tn,n) args k
  | eval_kw t:term$                               -> eval_term t
  | f:flag$ val_kw (n,k,t):val_def$               -> new_val f n k t
  | f:flag$ check_kw a:kind$ _:subset b:kind$     -> check_sub f a b
  | _:include_kw fn:string_lit$                   -> include_file fn
  | _:html_kw id:lident$                          -> output_html (in_pos _loc_id id)
  | latex_kw t:tex_text$             when not top -> Io.tex "%a%!" Latex.output t
  | _:set_kw "verbose" b:enables                  -> verbose := b
  | _:set_kw "texfile" fn:string_lit when not top -> Io.(fmts.tex <- fmt_of_file fn)
  | _:clear_kw                       when top     -> System.clear ()
  | {quit_kw | exit_kw}              when top     -> raise End_of_file

and kind_def = tex_name? uident kind_def_args "=" kind

and kind_def_args =
  | EMPTY                             -> ([], [])
  | "(" ks:(list_sep' uident ",") ")" -> ([], ks)
  | "(" os:(list_sep' lgident ",") ks:{"," (list_sep uident ",")}?[[]] ")"

and val_def =
  | r:is_rec n:int_lit? tex:tex_name? id:lident k:{":" kind}? "=" t:term ->
      let t =
        if not r then t else pfixY (in_pos _loc_id id, k) _loc_t n t
      in ((tex,id), k, t)

(****************************************************************************
 *                       High-level parsing functions                       *
 ****************************************************************************)

let toplevel_of_string : string -> unit =
  parse_string (command true) subml_blank

let full_of_string : string -> string -> unit = fun filename ->
  parse_string ~filename (parser _:(command false)*) subml_blank

let full_of_buffer : Input.buffer -> unit =
  parse_buffer (parser _:(command false)*) subml_blank

let eval_file =
  let eval_file fn =
    let buf = Io.file fn in
    Io.out "## loading file %S\n%!" fn;
    parse_buffer (parser _:(command false)*) subml_blank buf
  in
  read_file := eval_file; eval_file

let handle_exception : bool -> ('a -> 'b) -> 'a -> bool = fun intop fn v ->
  let pos1 = print_position in
  let pos2 ff (buf,pos) =
    let open Input in
    fprintf ff "File %S, line %d, characters %d" (fname buf) (line_num buf)
      (utf8_col_num buf pos)
  in
  try fn v; not intop with
  | End_of_file            -> true
  | System.Stopped         -> Io.err "\n[Interrupted]\n%!"; false
  | Arity_error(p,m)       -> Io.err "%a:\n%s\n%!" pos1 p m; false
  | Positivity_error(p,m)  -> Io.err "%a:\n%s\n%!" pos1 p m; false
  | Parse_error(buf,pos,_,_) -> Io.err "%a:\nSyntax error\n%!" pos2 (buf,pos);
                              false
  | Unbound(s)             -> Io.err "%a:\nUnbound: %s\n%!" pos1 s.pos s.elt;
    false
  | Error.Error l          -> Io.err "%a" Error.display_errors l; false
  | Loop_error             -> Io.err "Oups, loops\n%!"; false
  | e                      -> Io.err "Uncaught exception %s\n%!"
                                (Printexc.to_string e);
                              false
