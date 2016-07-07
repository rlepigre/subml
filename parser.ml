open Decap
open Bindlib
open Ast
open Location
open Print
open Eval
open Typing
open Raw
open Io

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

(* Blank function for basic blank characters (' ', '\t', '\r' and '\n'). *)
let tex_blank buf pos =
  let rec fn curr =
    let (buf, pos) = curr in
    let (c, buf', pos') = Input.read buf pos in
    let next = (buf', pos') in
    if List.mem c ['\t'; ' '; '\r'; '\n'] then fn next else curr
  in fn (buf,pos)

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
let parser tex_text = "{" l:latex_atom* "}" ->
  (fun () -> Latex.List (List.map (fun f -> f ()) l))

and latex_atom =
  | hash "witnesses" "#" ->
      (fun () -> Latex.Witnesses)
  | hash br:int_lit?[0] u:"!"? k:kind "#" ->
      (fun () -> Latex.Kind (br,u<>None, unbox (unsugar_kind empty_env k)))
  | "@" br:int_lit?[0] u:"!"? t:term "@" ->
      (fun () -> Latex.Term (br,u<>None, unbox (unsugar_term empty_env t)))
  | t:tex_simple ->
      (fun () -> Latex.Text t)
  | tex_text
  | hash "check" a:kind subset b:kind "#" ->
      (fun () ->
        let a = unbox (unsugar_kind empty_env a) in
        let b = unbox (unsugar_kind empty_env b) in
        let (prf, cg) = generic_subtype a b in
        Latex.SProof (prf, cg))
  | hash br:int_lit?[0] ":" id:lident "#" ->
      (fun () -> Latex.Kind (br, false, (Hashtbl.find val_env id).ttype))
  | hash br:int_lit?[0] "?" id:uident "#" ->
      (fun () -> Latex.KindDef (br, Hashtbl.find typ_env id))
  | "##" id:lident "#" ->
      (fun () -> Latex.TProof (Hashtbl.find val_env id).proof)
  | "#!" id:lident "#" ->
      (fun () -> Latex.Sct (Hashtbl.find val_env id).calls_graph)

(****************************************************************************
 *                       Top-level parsing functions                        *
 ****************************************************************************)

let latex_ch = ref stdout

let open_latex fn =
  if !latex_ch <> stdout then close_out !latex_ch;
  latex_ch := open_out fn

let parser enabled =
  | "on"  -> true
  | "off" -> false

let parser opt_flag =
  | "verbose" b:enabled -> (fun () -> verbose := b)
  | "texfile" fn:string_lit -> (fun () -> open_latex fn)
  | "print_term_in_subtyping" b:enabled -> (fun () -> Print.print_term_in_subtyping := b)

type command =
  | NewType of string option * string * string list * pkind
  | NewVal  of bool * string option * string * pkind * pterm * Location.t * Location.t
  | Check   of bool * pkind * pkind
  | Eval    of pterm
  | Include of string
  | Latex   of unit -> Latex.latex_output
  | Set     of unit -> unit

let parser command =
  | type_kw tex:tex_name? (name,args,k):kind_def   -> NewType(tex,name,args,k)
  | eval_kw t:term                                 -> Eval(t)
  | val_kw r:is_rec tex:tex_name? id:lident ":" k:kind "=" t:term
                                                   -> NewVal(r,tex,id,k,t,_loc_t,_loc_id)
  | check_kw n:is_not a:kind _:subset b:kind       -> Check(not n,a,b)
  | _:include_kw fn:string_lit                     -> Include(fn)
  | latex_kw t:(change_layout tex_text tex_blank)  -> Latex(t)
  | _:set_kw f:opt_flag                            -> Set(f)

and kind_def = uident {"(" ids:(list_sep' uident ",") ")"}?[[]] "=" kind

(****************************************************************************
 *                       High-level parsing functions                       *
 ****************************************************************************)

let read_file = ref (fun _ -> assert false)

let ignore_latex = ref false

let run_command : command -> unit = function
  (* Type definition command. *)
  | NewType(tex,name,args,k) ->
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
  (* Evaluate a term. *)
  | Eval(t) ->
      let t = unbox (unsugar_term empty_env t) in
      let _ = type_check t (new_uvar ()) in
      reset_all ();
      io.stdout "%a\n%!" (print_term true) (eval t)
  (* Typed value definition. *)
  | NewVal(r,tex,id,k,t,_loc_t,_loc_id) ->
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
  (* Check subtyping. *)
  | Check(n,a,b) ->
      let a = unbox (unsugar_kind empty_env a) in
      let b = unbox (unsugar_kind empty_env b) in
      begin
        try
          let (_prf, _) = generic_subtype a b in
          (* FIXME
          if not n then (
            io.stdout "MUST FAIL\n%!";
            print_subtyping_proof prf;
            failwith "check"
          );
          *)
          if !verbose then
            io.stderr "check %a < %a passed\n%!" (print_kind false) a (print_kind false) b;
          reset_epsilon_tbls ()
        with
        | Subtype_error s when n ->
           io.stdout "CHECK FAILED: OK %s\n%!" s;
           failwith "check"
        | Subtype_error s ->
            if !verbose then
              io.stderr "check not %a < %a passed\n%!" (print_kind false) a (print_kind false) b;
           reset_epsilon_tbls ();
        | e ->
           io.stdout "UNCAUGHT EXCEPTION: %s\n%!" (Printexc.to_string e);
           failwith "check"
      end
  (* Include a file. *)
  | Include(fn) ->
      let save = !ignore_latex in
      ignore_latex := true;
      !read_file fn;
      ignore_latex := save
  (* Latex. *)
  | Latex(t) ->
      if not !ignore_latex then Latex.output !latex_ch (t ())
  (* Set a flag. *)
  | Set(f) -> f ()

let parser toplevel =
  (* Regular commands. *)
  | c:command EOF           -> run_command c
  (* Clear the screen. *)
  | clear_kw EOF            -> ignore (Sys.command "clear")
  (* Exit the program. *)
  | {quit_kw | exit_kw} EOF -> raise End_of_file

let toplevel_of_string : string -> unit = fun s ->
  parse_string toplevel subml_blank s

let parser file_contents =
  | cs:command* EOF -> List.iter run_command cs

let eval_file fn =
  let buf = io.files fn in
  parse_buffer file_contents subml_blank buf;
  io.stdout "## file loaded %S\n%!" fn

let _ = read_file := eval_file
