open Pa_ocaml_prelude
open Decap
open Bindlib
open Util
open Ast
open Print
open Multi_print
open Eval
open Typing
open Proof_trace
open Print_trace
open Raw

#define LOCATE locate

(* Some combinators. *)
let list_sep elt sep = parser
  | EMPTY                        -> []
  | e:elt es:{_:STR(sep) e:elt}* -> e::es

let list_sep' elt sep = parser
  | e:elt es:{_:STR(sep) e:elt}* -> e::es

let list_sep'' elt sep = parser
  | e:elt es:{_:sep e:elt}+ -> e::es

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
  black_box f (Charset.singleton s.[0]) None s


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
let parser lambda : unit grammar = "λ" | fun_kw
let parser klam   : unit grammar = "Λ" | "/\\"
let parser dot    : unit grammar = "." | "->" | "→" | "↦"
let parser hole   : unit grammar = "?"
let parser comma  : unit grammar = ","

let parser pident = id:''[a-zA-Z0-9][a-zA-Z0-9_']*'' -> check_not_keyword id; id
let parser lident = id:''[a-z][a-zA-Z0-9_']*'' -> check_not_keyword id; id
let parser uident = id:''[A-Z][a-zA-Z0-9_']*'' -> check_not_keyword id; id

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
      -> in_pos _loc (PFAll(id,a))
  | exists id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PExis(id,a))
  | mu id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PMu(id,a))
  | nu id:uident a:(pkind KFunc) when p = KFunc
      -> in_pos _loc (PNu(id,a))
  | "{" fs:prod_items "}" when p = KAtom
      -> in_pos _loc (PProd(fs))
  | fs : kind_prod when p = KProd
      -> in_pos _loc (PProd(fs))
  | "[" fs:sum_items "]" when p = KAtom
			 -> in_pos _loc (PSum(fs))
  | t:(term TAtom) "." s:pident -> in_pos _loc (PDPrj(t,s))
  | hole when p = KAtom
      -> in_pos _loc PHole

  | "(" a:(pkind KFunc) ")" when p = KAtom
  | a:(pkind KAtom) when p = KProd
  | a:(pkind KProd) when p = KFunc

and kind_list  = l:(list_sep (pkind KFunc) ",")
and kind_prod  = l:(list_sep'' (pkind KAtom) time) -> List.mapi (fun i x -> (string_of_int (i+1), x)) l
and sum_item   = id:uident a:{_:of_kw a:(pkind KFunc)}?
and sum_items  = l:(list_sep sum_item "|")
and prod_item  = id:pident ":" a:(pkind KFunc)
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
  | klam x:uident t:(term TFunc) when p = TFunc ->
      in_pos _loc (PKAbs(in_pos _loc_x x,t))
  | t:(term TAppl) u:(term TColo) when p = TAppl ->
      in_pos _loc (PAppl(t,u))
  | t:(term TAppl) ";" u:(term TSeq) when p = TSeq ->
     sequence _loc t u
  | "print(" - s:string_lit - ")" when p = TAtom ->
      in_pos _loc (PPrnt(s))
  | c:uident uo:(term TAtom)? when p = TAtom ->
      in_pos _loc (PCstr(c,uo))
  | t:(term TAtom) "." l:pident when p = TAtom ->
      in_pos _loc (PProj(t,l))
  | case_kw t:(term TFunc) of_kw "|"?
    ps:(list_sep case "|") when p = TFunc ->
      in_pos _loc (PCase(t,ps))
  | "{" fs:(list_sep field ";") ";"? "}" when p = TAtom ->
     in_pos _loc (PReco(fs))
  | "(" fs:tuple ")" when p = TAtom ->
     in_pos _loc (PReco(fs))
  | t:(term TColo) ":" k:kind when p = TColo ->
      in_pos _loc (PCoer(t,k))
  | t:(term TAppl) "::" l:(term TSeq) when p = TSeq ->
      list_cons _loc t l
  | id:lident when p = TAtom ->
      in_pos _loc (PLVar(id))
  | fix_kw x:var dot u:(term TFunc) when p = TFunc ->
      in_pos _loc (PFixY(x,u))
  | "[" l:list "]" -> l
  | let_kw r:rec_kw? id:lvar "=" t:(term TFunc) in_kw u:(term TFunc) when p = TFunc ->
       let t =
	 if r = None then t
	 else in_pos _loc_t (PFixY(id, t)) in
       in_pos _loc (PAppl(in_pos _loc_u (PLAbs([id],u)), t))
  | "(" t:(term TFunc) ")" when p = TAtom
  | if_kw c:(term TFunc) then_kw t:(term TFunc) else_kw e:(term TFunc) ->
      in_pos _loc (PCase(c, [("True", None, t); ("False", None, e)]))
  | t:(term TAtom) when p = TColo
  | t:(term TColo) when p = TAppl
  | t:(term TAppl) when p = TSeq
  | t:(term TSeq) when p = TFunc

and pattern =
    | c:uident x:var? -> (c,x)
    | "[" "]"         -> ("Nil", None)

and case = (c,x):pattern _:arrow t:(term TFunc) -> (c, x, t)
and field   = l:pident k:{ ":" kind }? "=" t:(term TFunc) ->
    (l, match k with None -> t | Some k -> in_pos _loc (PCoer(t,k)))
and tuple   = l:(list_sep'' (term TFunc) comma) -> List.mapi (fun i x -> (string_of_int (i+1), x)) l
and list    = EMPTY -> list_nil _loc
            | t:(term TFunc) "," l:list -> list_cons _loc t l
let term = term TFunc

(****************************************************************************
 *                      High level parsing functions                        *
 ****************************************************************************)

exception Finish

let top_level_blank = blank_regexp ''[ \t\n\r]*''

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
  ) Charset.full_charset None "ANY"

let comment = change_layout (parser "(*" _:comment_char** "*)") no_blank

let parser blank_parser = _:comment**

let file_blank = blank_grammar blank_parser top_level_blank

let parser enabled =
  | "on"  -> true
  | "off" -> false

let latex_ch = ref stdout

let open_latex fn =
  if !latex_ch <> stdout then close_out !latex_ch;
  latex_ch := open_out fn

let parser opt_flag =
  | "verbose" b:enabled -> verbose := b
  | "latex" b:enabled -> Multi_print.print_mode := if b then Latex else Ascii
  | "texfile" fn:string_lit -> open_latex fn
  | "print_term_in_subtyping" b:enabled -> Print.print_term_in_subtyping := b

let read_file = ref (fun _ -> assert false)

let parser latex_atom =
  | "#" "witnesses" "#"     -> Latex_trace.Witnesses
  | "#" u:"!"? k:kind "#" -> Latex_trace.Kind (u<>None, unbox (unsugar_kind [] [] k))
  | "@" u:"!"? t:term "@" -> Latex_trace.Term (u<>None, unbox (unsugar_term [] [] t))
  | t:''[^}{@#]+''        -> Latex_trace.Text t
  | l:latex_text          -> l
  | "#?" a:kind {"⊂" | "⊆" | "<"} b:kind "#" ->
     let a = unbox (unsugar_kind [] [] a) in
     let b = unbox (unsugar_kind [] [] b) in
     generic_subtype a b;
     let prf = collect_subtyping_proof () in
     Latex_trace.SProof prf
  | "#:" id:lident "#"    -> let t = Hashtbl.find val_env id in
			     Latex_trace.Kind (false, t.ttype)
  | "#?" id:uident "#"    -> let t = Hashtbl.find typ_env id in
			     Latex_trace.KindDef t
  | "##" id:lident "#"    -> let t = Hashtbl.find val_env id in
			     Latex_trace.TProof t.proof


and latex_text = "{" l:latex_atom* "}" -> Latex_trace.List l

let parser latex_name_aux =
    | t:''[^{}]+''              -> Latex_trace.Text t
    | "{" l:latex_name_aux* "}" -> Latex_trace.List l

and latex_name = "{" t:latex_name_aux* "}" -> Latex_trace.to_string (Latex_trace.List t)

let ignore_latex = ref false

let parser command =
  (* Type definition command. *)
  | type_kw tex:latex_name? (name,args,k):kind_def ->
        let arg_names = Array.of_list args in
        let f args =
          let env = ref [] in
          Array.iteri (fun i k -> env := (arg_names.(i), k) :: !env) args;
          unsugar_kind [] !env k
        in
        let b = mbind mk_free_tvar arg_names f in
        let td =
          { tdef_name  = name
	  ; tdef_tex_name = (match tex with None -> "\\mathrm{"^name^"}" | Some s -> s)
          ; tdef_arity = Array.length arg_names
          ; tdef_value = unbox b }
        in
        Printf.fprintf stdout "%a\n%!" (print_kind_def false) td;
        Hashtbl.add typ_env name td
  (* Unfold a type definition. *)
  | unfold_kw k:kind ->
        let k = unbox (unsugar_kind [] [] k) in
        Printf.fprintf stdout "%a\n%!" (print_kind true) k
  (* Parse a term. *)
  | parse_kw t:term ->
        let t = unbox (unsugar_term [] [] t) in
        Printf.fprintf stdout "%a\n%!" (print_term false) t
  (* Evaluate a term. *)
  | eval_kw t:term ->
        let t = unbox (unsugar_term [] [] t) in
        let t = eval t in
        Printf.fprintf stdout "%a\n%!" (print_term false) t
  (* Typed value definition. *)
  | val_kw r:rec_kw? tex:latex_name? id:lident ":" k:kind "=" t:term ->
       let t =
	 if r = None then t
	 else in_pos _loc_t (PFixY((in_pos _loc_id id, Some k), t)) in
       let t = unbox (unsugar_term [] [] t) in
       let k = unbox (unsugar_kind [] [] k) in
       let prf =
	  try
	    type_check t k;
	    let prf = collect_typing_proof () in
	    if !verbose then print_typing_proof prf;
	    prf
	  with
	    e -> trace_backtrace (); raise e
	in
        reset_all ();
        let t = eval t in
        Hashtbl.add val_env id
	  { name = id
	  ; tex_name = (match tex with None -> "\\mathrm{"^id^"}" | Some s -> s)
	  ; value = t
	  ; ttype = k
	  ; proof = prf
	  };
        Printf.fprintf stdout "%s : %a\n%!" id (print_kind false) k
  (* Check subtyping. *)
  | check_kw n:{"not" -> false}?[true] a:kind {"⊂" | "⊆" | "<"} b:kind ->
        let a = unbox (unsugar_kind [] [] a) in
        let b = unbox (unsugar_kind [] [] b) in
        begin
          try
	    generic_subtype a b;
	    let prf = collect_subtyping_proof () in
	    if !verbose || not n then (
	      Printf.eprintf "MUST FAIL\n%!";
	      print_subtyping_proof prf;
	      exit 1
	    );
	    reset_epsilon_tbls ();
	    Printf.eprintf "check: OK\n%!"
          with
          | Subtype_error s when n ->
	     Printf.eprintf "CHECK FAILED: OK %s\n%!" s;
	     exit 1;
          | Subtype_error s ->
	     Printf.eprintf "check not: OK %s\n%!" s;
 	     trace_state := [];
	     reset_epsilon_tbls ();
          | e ->
	     Printf.eprintf "UNCAUGHT EXCEPTION: %s\n%!" (Printexc.to_string e);
	     exit 1;
        end
  | latex_kw t:latex_text ->
     if not !ignore_latex then Latex_trace.output !latex_ch t
  (* Include a file. *)
  | _:include_kw fn:string_lit ->
     let save = !ignore_latex in
     ignore_latex := true;
     !read_file fn;
     ignore_latex := save
  (* Set a flag. *)
  | _:set_kw f:opt_flag

let parser toplevel =
  (* Regular commands. *)
  | command
  (* Clear the screen. *)
  | clear_kw ->
      ignore (Sys.command "clear")
  (* Exit the program. *)
  | {quit_kw | exit_kw} ->
      raise Finish

let toplevel_of_string : string -> unit = fun s ->
  let parse = parse_string toplevel top_level_blank in
  Decap.handle_exception parse s

let parser file_contents =
  | cs:command** -> ()

let eval_file fn =
  Printf.printf "## Loading file %S\n%!" fn;
  let parse = parse_file file_contents file_blank in
  parse fn;
  Printf.printf "## file Loaded %S\n%!" fn

let _ = read_file := eval_file
