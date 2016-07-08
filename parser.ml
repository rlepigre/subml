open Decap
open Bindlib
open Ast
open Position
open Print
open Eval
open Typing
open Raw
open Io
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

let lident = ident lidentfirst
let uident = ident uppercase

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
let when_kw = new_keyword "when"
let type_kw = new_keyword "type"
let not_kw  = new_keyword "not"
let max_kw  = new_keyword "max"

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

let parser arrow  : unit grammar = "→" | "->"
let parser forall : unit grammar = "∀" | "/\\"
let parser exists : unit grammar = "∃" | "\\/"
let parser mu     : unit grammar = "μ" | "!"
let parser nu     : unit grammar = "ν" | "?"
let parser time   : unit grammar = "×" | "*"
let parser lambda : unit grammar = "λ"
let parser klam   : unit grammar = "Λ" | "/\\"
let parser dot    : unit grammar = "."
let parser mapto  : unit grammar = "->" | "→" | "↦"
let parser comma  : unit grammar = ","
let parser subset : unit grammar = "⊂" | "⊆" | "<"
let parser infty  : unit grammar = "∞"

let parser is_rec =
  | EMPTY  -> false
  | rec_kw -> true

let parser is_not =
  | EMPTY  -> false
  | not_kw -> true

let parser enables =
  | "on"  -> true
  | "off" -> false

(****************************************************************************
 *                  Parsers for ordinals and kinds (types)                  *
 ****************************************************************************)

(* Entry point for ordinals. *)
let parser ordinal : pordinal Decap.grammar =
  | infty?                  -> in_pos _loc PConv
  | s:lident                -> in_pos _loc (PVari s)
  | o:ordinal '+' n:int_lit -> padd _loc o n

(* Entry point for kinds. *)
let parser kind : pkind Decap.grammar = (pkind `Fun)

and kind_atm = (pkind `Atm)
and kind_prd = (pkind `Prd)

and pkind (p : [`Atm | `Prd | `Fun]) =
  | a:kind_prd arrow b:kind       when p = `Fun -> in_pos _loc (PFunc(a,b))
  | id:uident l:kind_args$        when p = `Atm -> in_pos _loc (PTVar(id,l))
  | forall id:uident a:kind       when p = `Fun -> in_pos _loc (PKAll(id,a))
  | exists id:uident a:kind       when p = `Fun -> in_pos _loc (PKExi(id,a))
  | forall id:lident a:kind       when p = `Fun -> in_pos _loc (POAll(id,a))
  | exists id:lident a:kind       when p = `Fun -> in_pos _loc (POExi(id,a))
  | mu o:ordinal id:uident a:kind when p = `Fun -> in_pos _loc (PFixM(o,id,a))
  | nu o:ordinal id:uident a:kind when p = `Fun -> in_pos _loc (PFixN(o,id,a))
  | "{" fs:kind_reco "}"          when p = `Atm -> in_pos _loc (PProd(fs))
  | fs:kind_prod                  when p = `Prd -> in_pos _loc (PProd(fs))
  | "[" fs:kind_dsum "]"          when p = `Atm -> in_pos _loc (PDSum(fs))
  | t:tatm "." s:uident       when p = `Atm -> in_pos _loc (PDPrj(t,s))
  | a:kind_atm (s,b):with_eq      when p = `Atm -> in_pos _loc (PWith(a,s,b))
  (* Parenthesis and coercions. *)
  | "(" kind ")"                  when p = `Atm
  | kind_atm                      when p = `Prd
  | kind_prd                      when p = `Fun

and kind_args = {"(" l:kind_list ")"}?[[]]
and kind_prod = fs:(glist_sep'' kind_atm time) -> build_prod fs
and kind_list = l:(list_sep kind ",")
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
  | fun_kw xs:var+ mapto t:term$  when p = `Lam -> in_pos _loc (PLAbs(xs,t))
  | klam x:uident t:term          when p = `Lam -> let x = in_pos _loc_x x in
                                                   in_pos _loc (PKAbs(x,t))
  | klam o:lident t:term          when p = `Lam -> let o = in_pos _loc_o o in
                                                   in_pos _loc (POAbs(o,t))
  | t:tapp u:tcol                 when p = `App -> in_pos _loc (PAppl(t,u))
  | t:tapp ";" u:tseq             when p = `Seq -> sequence _loc t u
  | "print(" - s:string_lit - ")" when p = `Atm -> in_pos _loc (PPrnt(s))
  | c:uident uo:{"[" term "]"}?$  when p = `Atm -> in_pos _loc (PCons(c,uo))
  | t:tatm "." l:lident           when p = `Atm -> in_pos _loc (PProj(t,l))
  | case_kw t:term of_kw ps:pats$ when p = `Lam -> in_pos _loc (PCase(t,ps))
  | "{" fs:term_reco "}"          when p = `Atm -> in_pos _loc (PReco(fs))
  | "(" fs:term_prod ")"          when p = `Atm -> in_pos _loc (PReco(fs))
  | t:tcol ":" k:kind$            when p = `Col -> in_pos _loc (PCoer(t,k))
  | id:lident                     when p = `Atm -> in_pos _loc (PLVar(id))
  | fix_kw x:var mapto u:term     when p = `Lam -> pfixY x _loc_u u
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
  | id:lident                    -> (in_pos _loc_id id, None)
  | "(" id:lident ":" k:kind ")" -> (in_pos _loc_id id, Some k)

and let_var =
  | id:lident            -> (in_pos _loc_id id, None)
  | id:lident ":" k:kind -> (in_pos _loc_id id, Some k)

and term_llet = let_kw r:is_rec id:let_var "=" t:term in_kw u:term ->
  let t = if not r then t else pfixY id _loc_t t in
  in_pos _loc (PAppl(in_pos _loc_u (PLAbs([id],u)), t))

and term_cond = if_kw c:term then_kw t:term else_kw e:term$ ->
  in_pos _loc (PCase(c, [("Tru", None, t); ("Fls", None, e)]))

and term_reco = (list_sep field ";") _:";"?
and term_prod = l:(glist_sep'' term comma) -> build_prod l

and field = l:lident k:{ ":" kind }?$ "=" t:tapp$ ->
  (l, match k with None -> t | Some k -> in_pos _loc (PCoer(t,k)))

and term_list =
  | EMPTY                  -> list_nil _loc
  | t:term "," l:term_list -> list_cons _loc t l

and pats = _:"|"? ps:(list_sep case "|")

and pattern =
  | c:uident x:{"[" x:var "]"}? -> (c,x)
  | "[" "]"                     -> ("Nil", None)

and case = (c,x):pattern _:arrow t:term -> (c, x, t)

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
      let (prf, cg) = generic_subtype a b in
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
let new_type : name -> string list -> pkind -> unit = fun name args k ->
  let (tex, name) = name in
  let arg_names = Array.of_list args in
  let tdef_arity = Array.length arg_names in
  let tdef_variance = Array.make tdef_arity Non in
  let f args =
    let env = ref [] in
    let f i k =
      let v = (k, (Reg(i,tdef_variance))) in
      env := (arg_names.(i), v) :: !env
    in
    Array.iteri f args;
    unsugar_kind {empty_env with kinds = !env} k
  in
  let b = mbind mk_free_kvari arg_names f in
  let tdef_tex_name =
    match tex with
    | None   -> "\\mathrm{"^name^"}"
    | Some s -> s
  in
  let td =
    { tdef_name = name ; tdef_tex_name ; tdef_arity ; tdef_variance
    ; tdef_value = unbox b }
  in
  if !verbose then io.stdout "%a\n%!" (print_kind_def false) td;
  Hashtbl.add typ_env name td

(* New value definition. *)
let new_val : bool -> name -> pkind -> pterm -> pos -> pos -> unit =
  fun r (tex,id) k t _loc_t _loc_id ->
    let t = if not r then t else pfixY (in_pos _loc_id id, Some k) _loc_t t in
    let t = unbox (unsugar_term empty_env t) in
    let k = unbox (unsugar_kind empty_env k) in
    let (prf, calls_graph) = type_check t k in
    reset_all ();
    let value = eval t in
    let tex_name =
      match tex with None -> "\\mathrm{"^id^"}" | Some s -> s
    in
    Hashtbl.add val_env id
      { name = id ; tex_name ; value ; orig_value = t ; ttype = k
      ; proof = prf ; calls_graph }

(* Check a subtyping relation. *)
let check_sub : bool -> pkind -> pkind -> unit = fun must_fail a b ->
  let a = unbox (unsugar_kind empty_env a) in
  let b = unbox (unsugar_kind empty_env b) in
  begin
    try ignore (generic_subtype a b) with
    | Subtype_error s ->
        if not must_fail then
          begin
            io.stdout "CHECK FAILED: %s\n%!" s;
            failwith "check"
          end
    | e               ->
        io.stdout "UNCAUGHT EXCEPTION: %s\n%!" (Printexc.to_string e);
        failwith "check"
  end;
  reset_epsilon_tbls ()

(* Evaluate a term. *)
let eval_term : pterm -> unit = fun t ->
  let t = unbox (unsugar_term empty_env t) in
  let (k,_,_) = type_infer t in
  reset_all ();
  io.stdout "%a : %a\n%!" (print_term true) (eval t) (print_kind true) k

(* Load a file. *)
let read_file : (string -> unit) ref = ref (fun _ -> assert false)
let include_file : string -> unit = fun fn ->
  let open Latex in
  let s = !ignore_latex in ignore_latex := true;
  (* FIXME should we save something else ? *)
  !read_file fn;
  ignore_latex := s

(* Output some TeX. *)
let output_tex : Latex.latex_output -> unit = fun t ->
  let open Latex in
  let ff = formatter_of_out_channel !latex_ch in
  if not !ignore_latex then output ff t

(****************************************************************************
 *                       Top-level parsing functions                        *
 ****************************************************************************)

let parser command top =
  | type_kw (tn,n,args,k):kind_def$               -> new_type (tn,n) args k
  | eval_kw t:term$                               -> eval_term t
  | val_kw r:is_rec tex:tex_name? id:lident ":" k:kind "=" t:term$ ->
      new_val r (tex,id) k t _loc_t _loc_id
  | check_kw n:is_not$ a:kind$ _:subset b:kind$   -> check_sub n a b
  | _:include_kw fn:string_lit$                   -> include_file fn
  | latex_kw t:tex_text$             when not top -> output_tex t
  | _:set_kw "verbose" b:enables                  -> verbose := b
  | _:set_kw "texfile" fn:string_lit when not top -> Latex.open_latex fn
  | _:clear_kw                       when top     -> System.clear ()
  | {quit_kw | exit_kw}              when top     -> raise End_of_file


and kind_def =
  | tn:tex_name? uident {"(" ids:(list_sep' uident ",") ")"}?[[]] "=" kind

let parser commands = _:(command false)*

(****************************************************************************
 *                       High-level parsing functions                       *
 ****************************************************************************)

let toplevel_of_string : string -> unit =
  parse_string (command true) subml_blank

let rec eval_file fn =
  read_file := eval_file;
  let buf = io.files fn in
  io.stdout "## loading file %S\n%!" fn;
  parse_buffer commands subml_blank buf
