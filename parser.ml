open Decap
open Bindlib
open Ast
open Print
open Eval
open Typing
open Proof_trace
open Print_trace
open Raw
open Io

let locate = Location.locate

#define LOCATE locate

exception Unclosed_comment of bool * string * int * int

let unclosed_comment : type a. (Input.buffer * int) -> a =
  fun (buf, pos) ->
    let line = Input.line_num buf in
    let fname = Input.fname buf in
    raise (Unclosed_comment (false, fname, line, pos))

let unclosed_comment_string : type a. (Input.buffer * int) -> a =
  fun (buf, pos) ->
    let line = Input.line_num buf in
    let fname = Input.fname buf in
    raise (Unclosed_comment (true, fname, line, pos))

(*
 * Characters to be ignored are:
 *   - ' ', '\t', '\r', '\n',
 *   - everything between "(*" and "*)" (ocaml-like comments).
 * Remarks on what is allowed inside an ocaml-like comment:
 *   - (nested) comments.
 *)
let subml_blank buf pos =
  let rec fn state stack prev curr =
    let (buf, pos) = curr in
    let (c, buf', pos') = Input.read buf pos in
    let next = (buf', pos') in
    match (state, stack, c) with
    (* Basic blancs. *)
    | (`Ini      , []  , ' '     )
    | (`Ini      , []  , '\t'    )
    | (`Ini      , []  , '\r'    )
    | (`Ini      , []  , '\n'    ) -> fn `Ini stack curr next
    (* Comment opening. *)
    | (`Ini      , _   , '('     ) -> fn (`Opn(curr)) stack curr next
    | (`Ini      , []  , _       ) -> curr
    | (`Opn(p)   , _   , '*'     ) -> fn `Ini (p::stack) curr next
    | (`Opn(_)   , _::_, '"'     ) -> fn (`Str(curr)) stack curr next (*#*)
    | (`Opn(_)   , _::_, '{'     ) -> fn (`SOp([],curr)) stack curr next (*#*)
    | (`Opn(_)   , []  , _       ) -> prev
    | (`Opn(_)   , _   , _       ) -> fn `Ini stack curr next
    (* String litteral in a comment (including the # rules). *)
    | (`Ini      , _::_, '"'     ) -> fn (`Str(curr)) stack curr next
    | (`Str(_)   , _::_, '"'     ) -> fn `Ini stack curr next
    | (`Str(p)   , _::_, '\\'    ) -> fn (`Esc(p)) stack curr next
    | (`Esc(p)   , _::_, _       ) -> fn (`Str(p)) stack curr next
    | (`Str(p)   , _::_, '\255'  ) -> unclosed_comment_string p
    | (`Str(_)   , _::_, _       ) -> fn state stack curr next
    | (`Str(_)   , []  , _       ) -> assert false (* Impossible. *)
    | (`Esc(_)   , []  , _       ) -> assert false (* Impossible. *)
    (* Delimited string litteral in a comment. *)
    | (`Ini      , _::_, '{'     ) -> fn (`SOp([],curr)) stack curr next
    | (`SOp(l,p) , _::_, 'a'..'z')
    | (`SOp(l,p) , _::_, '_'     ) -> fn (`SOp(c::l,p)) stack curr next
    | (`SOp(_,_) , p::_, '\255'  ) -> unclosed_comment p
    | (`SOp(l,p) , _::_, '|'     ) -> fn (`SIn(List.rev l,p)) stack curr next
    | (`SOp(_,_) , _::_, _       ) -> fn `Ini stack curr next
    | (`SIn(l,p) , _::_, '|'     ) -> fn (`SCl(l,(l,p))) stack curr next
    | (`SIn(_,p) , _::_, '\255'  ) -> unclosed_comment_string p
    | (`SIn(_,_) , _::_, _       ) -> fn state stack curr next
    | (`SCl([],b), _::_, '}'     ) -> fn `Ini stack curr next
    | (`SCl([],b), _::_, '\255'  ) -> unclosed_comment_string (snd b)
    | (`SCl([],b), _::_, _       ) -> fn (`SIn(b)) stack curr next
    | (`SCl(l,b) , _::_, c       ) -> if c = List.hd l then
                                        let l = List.tl l in
                                        fn (`SCl(l, b)) stack curr next
                                      else
                                        fn (`SIn(b)) stack curr next
    | (`SOp(_,_) , []  , _       ) -> assert false (* Impossible. *)
    | (`SIn(_,_) , []  , _       ) -> assert false (* Impossible. *)
    | (`SCl(_,_) , []  , _       ) -> assert false (* Impossible. *)
    (* Comment closing. *)
    | (`Ini      , _::_, '*'     ) -> fn `Cls stack curr next
    | (`Cls      , _::_, '*'     ) -> fn `Cls stack curr next
    | (`Cls      , _::s, ')'     ) -> fn `Ini s curr next
    | (`Cls      , _::_, _       ) -> fn `Ini stack curr next
    | (`Cls      , []  , _       ) -> assert false (* Impossible. *)
    (* Comment contents (excluding string litterals). *)
    | (`Ini     , p::_, '\255'  ) -> unclosed_comment p
    | (`Ini     , _::_, _       ) -> fn `Ini stack curr next
  in
  fn `Ini [] (buf, pos) (buf, pos)

let latex_blank buf pos =
  let rec fn curr =
    let (buf, pos) = curr in
    let (c, buf', pos') = Input.read buf pos in
    let next = (buf', pos') in
    if List.mem c ['\t'; ' '; '\n'] then fn next else curr
  in fn (buf,pos)

(* Keyword management. *)
let keywords = Hashtbl.create 20

let is_keyword : string -> bool = Hashtbl.mem keywords

let check_not_keyword : string -> unit = fun s ->
  if is_keyword s then
    give_up ("\""^s^"\" is a reserved identifier...")

let new_keyword : string -> unit grammar = fun s ->
  let ls = String.length s in
  if ls < 1 then
    raise (Invalid_argument "invalid keyword");
  if Hashtbl.mem keywords s then
    raise (Invalid_argument "keyword already defied");
  Hashtbl.add keywords s s;
  let f str pos =
    let str = ref str in
    let pos = ref pos in
    for i = 0 to ls - 1 do
      let (c,str',pos') = Input.read !str !pos in
      if c <> s.[i] then
        give_up ("The keyword "^s^" was expected...");
      str := str'; pos := pos'
    done;
    let (c,_,_) = Input.read !str !pos in
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' ->
        give_up ("The keyword "^s^" was expected...")
    | _                                           -> ((), !str, !pos)
  in
  black_box f (Charset.singleton s.[0]) false s

(* Some combinators. *)
let glist_sep elt sep = parser
  | EMPTY -> []
  | e:elt es:{_:sep e:elt}* -> e::es

let glist_sep' elt sep = parser
  | e:elt es:{_:sep e:elt}* -> e::es

let glist_sep'' elt sep = parser
  | e:elt es:{_:sep e:elt}+ -> e::es

let list_sep   elt sep = glist_sep   elt (string sep ())
let list_sep'  elt sep = glist_sep'  elt (string sep ())
let list_sep'' elt sep = glist_sep'' elt (string sep ())


let parser string_char =
  | "\\\"" -> "\""
  | "\\\\" -> "\\"
  | "\\n"  -> "\n"
  | "\\t"  -> "\t"
  | c:ANY  -> if c = '\\' || c = '"' || c = '\r' then give_up "";
              String.make 1 c

let string_lit =
  let slit = parser "\"" cs:string_char* "\"" -> String.concat "" cs in
  change_layout slit no_blank

let int_of_chars s =
  List.fold_left (fun acc c -> acc * 10 + (Char.code c - Char.code '0')) 0 (List.rev s)

let string_of_chars s =
  let s = Array.of_list s in
  let res = String.make (Array.length s) ' ' in
  Array.iteri (fun i c -> res.[i] <- c) s;
  res

let digit     = Charset.range '0' '9'
let lowercase = Charset.range 'a' 'z'
let uppercase = Charset.range 'A' 'Z'
let underscore = Charset.singleton '_'
let identany  = Charset.union (Charset.union lowercase uppercase) (Charset.union digit underscore)
let lidentfirst = Charset.union lowercase (Charset.union digit underscore)

let int_lit = change_layout (
    parser s:(in_charset digit)* -> int_of_chars s
  ) no_blank

let parser lident =
  id:(change_layout (
       parser c:(in_charset lidentfirst) s:(in_charset identany)* s':'\''*
         -> string_of_chars (c::s@s')
     ) no_blank) -> check_not_keyword id; id

let parser uident =
  id:(change_layout (
       parser c:(in_charset uppercase)  s:(in_charset identany)* s':'\''*
         -> string_of_chars (c::s@s')
     ) no_blank) -> check_not_keyword id; id

(* t ; u => (fun (x : unit) -> u) t *)
let sequence pos t u =
  in_pos pos (
    PAppl(in_pos pos (
      PLAbs([in_pos pos "_",Some (in_pos pos (
        PProd []))] ,u)), t))

(* Basic tokens. *)
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

let parser is_rec =
  | EMPTY  -> false
  | rec_kw -> true

let parser is_not =
  | EMPTY  -> false
  | not_kw -> true

(****************************************************************************
 *                         A parser for kinds (types)                       *
 ****************************************************************************)

type pkind_prio = KFunc | KProd | KAtom

type pterm_prio = TFunc | TSeq | TAppl | TColo | TAtom

let parser pkind p =
  | a:(pkind KProd) arrow b:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PFunc(a,b))
  | id:uident l:{"(" l:kind_list ")"}?[[]] when p = KAtom
      -> in_pos _loc (PTVar(id,l))
  | forall id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PKAll(id,a))
  | exists id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PKExi(id,a))
  | mu id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PFixM(None,id,a))
  | nu id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PFixN(None,id,a))
  | "{" fs:prod_items "}" when p = KAtom
      -> in_pos _loc (PProd(fs))
  | fs : kind_prod when p = KProd
      -> in_pos _loc (PProd(fs))
  | "[" fs:sum_items "]" when p = KAtom
      -> in_pos _loc (PDSum(fs))
  | t:(term TAtom) "." s:uident -> in_pos _loc (PDPrj(t,s))
  | a:(pkind KAtom) with_kw s:uident "=" b:(pkind KAtom) when p = KAtom
      -> in_pos _loc (PWith(a,s,b))
  | "(" a:(pkind KFunc) ")" when p = KAtom
  | a:(pkind KAtom) when p = KProd
  | a:(pkind KProd) when p = KFunc

and kind_list  = l:(list_sep (pkind KFunc) ",")
and kind_prod  = l:(glist_sep'' (pkind KAtom) time) ->
  List.mapi (fun i x -> (string_of_int (i+1), x)) l
and sum_item   = id:uident a:{_:of_kw a:(pkind KFunc)}?
and sum_items  = l:(list_sep sum_item "|")
and prod_item  = id:lident ":" a:(pkind KFunc)
and prod_items = l:(list_sep prod_item ";")

and kind = (pkind KFunc)

and kind_def =
  | id:uident args:{"(" ids:(list_sep' uident ",") ")"}?[[]] "=" k:kind

(****************************************************************************
 *                          A parser for expressions                        *
 ****************************************************************************)

and var =
  | id:lident                    -> (in_pos _loc_id id, None)
  | "(" id:lident ":" k:kind ")" -> (in_pos _loc_id id, Some k)

and lvar =
  | id:lident                    -> (in_pos _loc_id id, None)
  | id:lident ":" k:kind         -> (in_pos _loc_id id, Some k)


and term p =
  | lambda xs:var+ dot t:(term TFunc) when p = TFunc ->
      in_pos _loc (PLAbs(xs,t))
  | fun_kw xs:var+ mapto t:(term TFunc) when p = TFunc ->
      in_pos _loc (PLAbs(xs,t))
  | klam x:uident t:(term TFunc) when p = TFunc ->
    in_pos _loc (PKAbs(in_pos _loc_x x,t))
  | t:(term TAppl) u:(term TColo) when p = TAppl ->
      in_pos _loc (PAppl(t,u))
  | "print(" - s:string_lit - ")" when p = TAtom ->
      in_pos _loc (PPrnt(s))
  | c:uident uo:{"[" (term TFunc) "]"}? when p = TAtom ->
      in_pos _loc (PCons(c,uo))
  | t:(term TAtom) "." l:lident when p = TAtom ->
    in_pos _loc (PProj(t,l))
  | case_kw t:(term TFunc) of_kw "|"? ps:(list_sep case "|") when p = TFunc ->
      in_pos _loc (PCase(t,ps))
  | "{" fs:(list_sep field ";") ";"? "}" when p = TAtom ->
     in_pos _loc (PReco(fs))
  | "(" fs:tuple ")" when p = TAtom ->
     (match fs with
     | [] -> assert false
     | [(_,t)] -> t
     | _ -> in_pos _loc (PReco(fs)))
  | t:(term TColo) ":" k:kind when p = TColo ->
    in_pos _loc (PCoer(t,k))
  | id:lident when p = TAtom ->
     in_pos _loc (PLVar(id))
  | fix_kw x:var mapto u:(term TFunc) when p = TFunc ->
    in_pos _loc (PFixY(x,u))
  | "[" l:list "]" -> l
  | let_kw r:is_rec id:lvar "=" t:(term TFunc) in_kw u:(term TFunc) when p = TFunc ->
     let t =
       if r then t
       else in_pos _loc_t (PFixY(id, t)) in
     in_pos _loc (PAppl(in_pos _loc_u (PLAbs([id],u)), t))
  | if_kw c:(term TFunc) then_kw t:(term TFunc) else_kw e:(term TFunc) ->
     in_pos _loc (PCase(c, [("Tru", None, t); ("Fls", None, e)]))
  | t:(term TAtom)  when p = TColo
  | t:(term TColo)  when p = TAppl
  | t:(term TAppl) f:{"::" u:(term TSeq) -> fun t -> list_cons _loc t u
		    | ";"  u:(term TSeq) -> fun t -> sequence  _loc t u
		                         }?[fun i -> i] when p = TSeq -> f t
  | t:(term TSeq) when p = TFunc

and pattern =
  | c:uident x:{"[" x:var "]"}? -> (c,x)
  | "[" "]"                     -> ("Nil", None)

and case = (c,x):pattern _:arrow t:(term TFunc) -> (c, x, t)
and field   = l:lident k:{ ":" kind }? "=" t:(term TFunc) ->
    (l, match k with None -> t | Some k -> in_pos _loc (PCoer(t,k)))
and tuple   = l:(glist_sep' (term TFunc) comma) -> List.mapi (fun i x -> (string_of_int (i+1), x)) l
and list    = EMPTY -> list_nil _loc
            | t:(term TFunc) "," l:list -> list_cons _loc t l
let term = term TFunc

(****************************************************************************
 *                      High level parsing functions                        *
 ****************************************************************************)

exception Finish

let comment_char = black_box
  (fun str pos ->
    let (c, str', pos') = Input.read str pos in
    match c with
    | '\255' -> give_up "Unclosed comment."
    | '*'    ->
        let (c', _, _) = Input.read str' pos' in
        if c' = ')' then
          give_up "Not the place to close a comment."
        else
          ((), str', pos')
    | _      -> ((), str', pos')
  ) Charset.full_charset false "ANY"

let parser enabled =
  | "on"  -> true
  | "off" -> false

let latex_ch = ref stdout

let open_latex fn =
  if !latex_ch <> stdout then close_out !latex_ch;
  latex_ch := open_out fn

let parser opt_flag =
  | "verbose" b:enabled -> (fun () -> verbose := b)
  | "texfile" fn:string_lit -> (fun () -> open_latex fn)
  | "print_term_in_subtyping" b:enabled -> (fun () -> Print.print_term_in_subtyping := b)

let read_file = ref (fun _ -> assert false)

let no_hash =
  Decap.test ~name:"no_hash" Charset.full_charset (fun buf pos ->
    let c,buf,pos = Input.read buf pos in
    if c <> '#' then ((), true) else ((), false))

let parser hash = "#" no_hash

let parser latex_atom =
  | hash "witnesses" "#"     ->
     (fun () -> Latex_trace.Witnesses)
  | hash br:int_lit?[0] u:"!"? k:kind "#" ->
     (fun () -> Latex_trace.Kind (br,u<>None, unbox (unsugar_kind empty_env k)))
  | "@" br:int_lit?[0] u:"!"? t:term "@" ->
     (fun () -> Latex_trace.Term (br,u<>None, unbox (unsugar_term empty_env t)))
  | t:(Decap.(change_layout (parser (in_charset Charset.(List.fold_left del full_charset ['}';'{';'@';'#']))+) no_blank)) ->
     (fun () -> Latex_trace.Text (string_of_chars t))
  | l:latex_text          -> l
  | hash "check" a:kind subset b:kind "#" -> (fun () ->
     let a = unbox (unsugar_kind empty_env a) in
     let b = unbox (unsugar_kind empty_env b) in
     generic_subtype a b;
     let prf, calls = collect_subtyping_proof () in
     let calls = match calls with
     | [c] -> c | _ -> assert false
     in
     Latex_trace.SProof (prf, calls))
  | hash br:int_lit?[0] ":" id:lident "#"    -> (fun () ->
     let t = Hashtbl.find val_env id in
     Latex_trace.Kind (br, false, t.ttype))
  | hash br:int_lit?[0] "?" id:uident "#"    -> (fun () ->
     let t = Hashtbl.find typ_env id in
     Latex_trace.KindDef(br,t))
  | "##" id:lident "#"    -> (fun () ->
     let t = Hashtbl.find val_env id in
     Latex_trace.TProof t.proof)
  | "#!" id:lident "#" -> (fun () ->
     let t = Hashtbl.find val_env id in
     Latex_trace.Sct t.calls)

and latex_text = "{" l:latex_atom* "}" -> (fun () ->
  Latex_trace.List (List.map (fun f -> f ()) l))

let parser latex_name_aux =
  | t:(Decap.(change_layout (parser (in_charset Charset.(List.fold_left del full_charset ['}';'{';'@';'#']))+) no_blank)) -> (fun () -> Latex_trace.Text (string_of_chars t))
  | "{" l:latex_name_aux* "}" -> (fun () -> Latex_trace.List (List.map (fun f -> f ()) l))

and latex_name = "{" t:latex_name_aux* "}" -> (fun () ->
  Latex_trace.to_string (Latex_trace.List (List.map (fun f -> f ()) t)))

let ignore_latex = ref false

type command =
  | NewType of (unit -> string) option * string * string list * pkind
  | NewVal  of bool * (unit -> string) option * string * pkind * pterm * Location.t * Location.t
  | Check   of bool * pkind * pkind
  | UnfoldK of pkind
  | ParseT  of pterm
  | Eval    of pterm
  | Include of string
  | Latex   of unit -> Latex_trace.latex_output
  | Set     of unit -> unit

let parser command =
  | type_kw tex:latex_name? (name,args,k):kind_def -> NewType(tex,name,args,k)
  | unfold_kw k:kind                               -> UnfoldK(k)
  | parse_kw t:term                                -> ParseT(t)
  | eval_kw t:term                                 -> Eval(t)
  | val_kw r:is_rec tex:latex_name?
      id:lident ":" k:kind "=" t:term              -> NewVal(r,tex,id,k,t,_loc_t,_loc_id)
  | check_kw n:is_not a:kind _:subset b:kind       -> Check(not n,a,b)
  | _:include_kw fn:string_lit                     -> Include(fn)
  | latex_kw t:(change_layout latex_text latex_blank) -> Latex(t)
  | _:set_kw f:opt_flag                            -> Set(f)

let run_command : command -> unit = function
  (* Type definition command. *)
  | NewType(tex,name,args,k) ->
      let arg_names = Array.of_list args in
      let f args =
        let env = ref [] in
        Array.iteri (fun i k -> env := (arg_names.(i), k) :: !env) args;
        unsugar_kind {empty_env with kinds = !env} k
      in
      let b = mbind mk_free_tvar arg_names f in
      let tex_name =
        match tex with
        | None   -> "\\mathrm{"^name^"}"
        | Some s -> s ()
      in
      let td =
        { tdef_name  = name
        ; tdef_tex_name = tex_name
        ; tdef_arity = Array.length arg_names
        ; tdef_value = unbox b }
      in
      Hashtbl.add typ_env name td
  (* Unfold a type definition. *)
  | UnfoldK(k) ->
      let k = unbox (unsugar_kind empty_env k) in
      io.stdout "%a\n%!" (print_kind true) k
  (* Parse a term. *)
  | ParseT(t) ->
      let t = unbox (unsugar_term empty_env t) in
      io.stdout "%a\n%!" (print_term false) t
  (* Evaluate a term. *)
  | Eval(t) ->
      let t = unbox (unsugar_term empty_env t) in
      begin
        try type_check t (new_uvar ());
        with e -> trace_backtrace (); raise e
      end;
      let _ = collect_typing_proof () in
      reset_all ();
      io.stdout "%a\n%!" (print_term true) (eval t)
  (* Typed value definition. *)
  | NewVal(r,tex,id,k,t,_loc_t,_loc_id) ->
      let t =
        if not r then t
        else in_pos _loc_t (PFixY((in_pos _loc_id id, Some k), t))
      in
      let t = unbox (unsugar_term empty_env t) in
      let k = unbox (unsugar_kind empty_env k) in
      let prf, calls =
        try
          type_check t k;
          let prf, calls = collect_typing_proof () in
          if !verbose then print_typing_proof prf;
          prf, calls
        with e -> trace_backtrace (); raise e
      in
      reset_all ();
      let tn = eval t in
      Hashtbl.add val_env id
        { name = id
        ; tex_name = (match tex with None -> "\\mathrm{"^id^"}" | Some s -> s ())
        ; value = tn
        ; orig_value = t
        ; ttype = k
        ; proof = prf
	; calls
        }
  (* Check subtyping. *)
  | Check(n,a,b) ->
      let a = unbox (unsugar_kind empty_env a) in
      let b = unbox (unsugar_kind empty_env b) in
      begin
        try
          generic_subtype a b;
          let prf, _ = collect_subtyping_proof () in
          if !verbose || not n then (
            io.stdout "MUST FAIL\n%!";
            print_subtyping_proof prf;
            failwith "check"
          );
          reset_epsilon_tbls ()
        with
        | Subtype_error s when n ->
           io.stdout "CHECK FAILED: OK %s\n%!" s;
           failwith "check"
        | Subtype_error s ->
           reset trace_state;
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
      if not !ignore_latex then Latex_trace.output !latex_ch (t ())
  (* Set a flag. *)
  | Set(f) -> f ()

let parser toplevel =
  (* Regular commands. *)
  | c:command EOF           -> run_command c
  (* Clear the screen. *)
  | clear_kw EOF            -> ignore (Sys.command "clear")
  (* Exit the program. *)
  | {quit_kw | exit_kw} EOF -> raise Finish

let toplevel_of_string : string -> unit = fun s ->
  parse_string toplevel subml_blank s

let parser file_contents =
  | cs:command* EOF -> List.iter run_command cs

let eval_file fn =
  let buf = io.files fn in
  parse_buffer file_contents subml_blank buf;
  io.stdout "## file Loaded %S\n%!" fn

let _ = read_file := eval_file
