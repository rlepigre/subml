open Decap
open Bindlib
open Util
open Ast
open Print
open Eval
open Typing
open Proof_trace
open Print_trace
open Raw
let locate = Location.locate
let keywords = Hashtbl.create 20
let is_keyword: string -> bool = Hashtbl.mem keywords
let check_not_keyword: string -> unit =
  fun s  ->
    if is_keyword s
    then give_up ("\"" ^ (s ^ "\" is a reserved identifier..."))
let new_keyword: string -> unit grammar =
  fun s  ->
    let ls = String.length s in
    if ls < 1 then raise (Invalid_argument "invalid keyword");
    if Hashtbl.mem keywords s
    then raise (Invalid_argument "keyword already defied");
    Hashtbl.add keywords s s;
    (let f str pos =
       let str = ref str in
       let pos = ref pos in
       for i = 0 to ls - 1 do
         (let (c,str',pos') = Input.read (!str) (!pos) in
          if c <> (s.[i])
          then give_up ("The keyword " ^ (s ^ " was expected..."));
          str := str';
          pos := pos')
       done;
       (let (c,_,_) = Input.read (!str) (!pos) in
        match c with
        | 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\'' ->
            give_up ("The keyword " ^ (s ^ " was expected..."))
        | _ -> ((), (!str), (!pos))) in
     black_box f (Charset.singleton (s.[0])) None s)
let glist_sep elt sep =
  Decap.alternatives
    [Decap.apply (fun _  -> []) (Decap.empty ());
    Decap.sequence elt
      (Decap.apply List.rev
         (Decap.fixpoint' []
            (Decap.apply (fun x  -> fun l  -> x :: l)
               (Decap.sequence sep elt (fun _  -> fun e  -> e)))))
      (fun e  -> fun es  -> e :: es)]
let glist_sep' elt sep =
  Decap.sequence elt
    (Decap.apply List.rev
       (Decap.fixpoint' []
          (Decap.apply (fun x  -> fun l  -> x :: l)
             (Decap.sequence sep elt (fun _  -> fun e  -> e)))))
    (fun e  -> fun es  -> e :: es)
let glist_sep'' elt sep =
  Decap.sequence elt
    (Decap.apply List.rev
       (Decap.fixpoint1' []
          (Decap.apply (fun x  -> fun l  -> x :: l)
             (Decap.sequence sep elt (fun _  -> fun e  -> e)))))
    (fun e  -> fun es  -> e :: es)
let list_sep elt sep = glist_sep elt (string sep ())
let list_sep' elt sep = glist_sep' elt (string sep ())
let list_sep'' elt sep = glist_sep'' elt (string sep ())
let string_char = Decap.declare_grammar "string_char"
let _ =
  Decap.set_grammar string_char
    (Decap.alternatives
       [Decap.apply (fun _  -> "\"") (Decap.string "\\\"" "\\\"");
       Decap.apply (fun _  -> "\\") (Decap.string "\\\\" "\\\\");
       Decap.apply (fun _  -> "\n") (Decap.string "\\n" "\\n");
       Decap.apply (fun _  -> "\t") (Decap.string "\\t" "\\t");
       Decap.apply
         (fun c  ->
            if (c = '\\') || ((c = '"') || (c = '\r')) then give_up "";
            String.make 1 c) Decap.any])
let string_lit =
  let slit =
    Decap.fsequence (Decap.string "\"" "\"")
      (Decap.sequence
         (Decap.apply List.rev
            (Decap.fixpoint []
               (Decap.apply (fun x  -> fun l  -> x :: l) string_char)))
         (Decap.string "\"" "\"")
         (fun cs  -> fun _  -> fun _  -> String.concat "" cs)) in
  change_layout slit no_blank
let int_of_chars s =
  List.fold_left
    (fun acc  -> fun c  -> (acc * 10) + ((Char.code c) - (Char.code '0'))) 0
    (List.rev s)
let string_of_chars s =
  let s = Array.of_list s in
  let res = String.make (Array.length s) ' ' in
  Array.iteri (fun i  -> fun c  -> res.[i] <- c) s; res
let digit = Charset.range '0' '9'
let lowercase = Charset.range 'a' 'z'
let uppercase = Charset.range 'A' 'Z'
let underscore = Charset.singleton '_'
let identany =
  Charset.union (Charset.union lowercase uppercase)
    (Charset.union digit underscore)
let lidentfirst = Charset.union lowercase (Charset.union digit underscore)
let int_lit =
  change_layout
    (delim
       (Decap.apply (fun s  -> int_of_chars s)
          (Decap.apply List.rev
             (Decap.fixpoint' []
                (Decap.apply (fun x  -> fun l  -> x :: l) (in_charset digit))))))
    no_blank
let lident = Decap.declare_grammar "lident"
let _ =
  Decap.set_grammar lident
    (Decap.apply (fun id  -> check_not_keyword id; id)
       (change_layout
          (delim
             (Decap.fsequence (in_charset lidentfirst)
                (Decap.sequence
                   (Decap.apply List.rev
                      (Decap.fixpoint' []
                         (Decap.apply (fun x  -> fun l  -> x :: l)
                            (in_charset identany))))
                   (Decap.apply List.rev
                      (Decap.fixpoint' []
                         (Decap.apply (fun x  -> fun l  -> x :: l)
                            (Decap.char '\'' '\''))))
                   (fun s  ->
                      fun s'  -> fun c  -> string_of_chars ((c :: s) @ s')))))
          no_blank))
let uident = Decap.declare_grammar "uident"
let _ =
  Decap.set_grammar uident
    (Decap.apply (fun id  -> check_not_keyword id; id)
       (change_layout
          (delim
             (Decap.fsequence (in_charset uppercase)
                (Decap.sequence
                   (Decap.apply List.rev
                      (Decap.fixpoint' []
                         (Decap.apply (fun x  -> fun l  -> x :: l)
                            (in_charset identany))))
                   (Decap.apply List.rev
                      (Decap.fixpoint' []
                         (Decap.apply (fun x  -> fun l  -> x :: l)
                            (Decap.char '\'' '\''))))
                   (fun s  ->
                      fun s'  -> fun c  -> string_of_chars ((c :: s) @ s')))))
          no_blank))
let sequence pos t u =
  in_pos pos
    (PAppl
       ((in_pos pos
           (PLAbs ([((in_pos pos "_"), (Some (in_pos pos (PProd []))))], u))),
         t))
let case_kw = new_keyword "case"
let rec_kw = new_keyword "rec"
let let_kw = new_keyword "let"
let val_kw = new_keyword "val"
let of_kw = new_keyword "of"
let in_kw = new_keyword "in"
let fix_kw = new_keyword "fix"
let fun_kw = new_keyword "fun"
let if_kw = new_keyword "if"
let then_kw = new_keyword "then"
let else_kw = new_keyword "else"
let with_kw = new_keyword "with"
let when_kw = new_keyword "when"
let type_kw = new_keyword "type"
let unfold_kw = new_keyword "unfold"
let clear_kw = new_keyword "clear"
let parse_kw = new_keyword "parse"
let quit_kw = new_keyword "quit"
let exit_kw = new_keyword "exit"
let eval_kw = new_keyword "eval"
let set_kw = new_keyword "set"
let include_kw = new_keyword "include"
let check_kw = new_keyword "check"
let latex_kw = new_keyword "latex"
let (arrow :unit grammar)= Decap.declare_grammar "arrow"
let _ =
  Decap.set_grammar arrow
    (Decap.alternatives
       [Decap.apply (fun _  -> ())
          (Decap.string "\226\134\146" "\226\134\146");
       Decap.apply (fun _  -> ()) (Decap.string "->" "->")])
let (forall :unit grammar)= Decap.declare_grammar "forall"
let _ =
  Decap.set_grammar forall
    (Decap.alternatives
       [Decap.apply (fun _  -> ())
          (Decap.string "\226\136\128" "\226\136\128");
       Decap.apply (fun _  -> ()) (Decap.string "/\\" "/\\")])
let (exists :unit grammar)= Decap.declare_grammar "exists"
let _ =
  Decap.set_grammar exists
    (Decap.alternatives
       [Decap.apply (fun _  -> ())
          (Decap.string "\226\136\131" "\226\136\131");
       Decap.apply (fun _  -> ()) (Decap.string "\\/" "\\/")])
let (mu :unit grammar)= Decap.declare_grammar "mu"
let _ =
  Decap.set_grammar mu
    (Decap.alternatives
       [Decap.apply (fun _  -> ()) (Decap.string "\206\188" "\206\188");
       Decap.apply (fun _  -> ()) (Decap.string "!" "!")])
let (nu :unit grammar)= Decap.declare_grammar "nu"
let _ =
  Decap.set_grammar nu
    (Decap.alternatives
       [Decap.apply (fun _  -> ()) (Decap.string "\206\189" "\206\189");
       Decap.apply (fun _  -> ()) (Decap.string "?" "?")])
let (time :unit grammar)= Decap.declare_grammar "time"
let _ =
  Decap.set_grammar time
    (Decap.alternatives
       [Decap.apply (fun _  -> ()) (Decap.string "\195\151" "\195\151");
       Decap.apply (fun _  -> ()) (Decap.string "*" "*")])
let (lambda :unit grammar)= Decap.declare_grammar "lambda"
let _ =
  Decap.set_grammar lambda
    (Decap.apply (fun _  -> ()) (Decap.string "\206\187" "\206\187"))
let (klam :unit grammar)= Decap.declare_grammar "klam"
let _ =
  Decap.set_grammar klam
    (Decap.alternatives
       [Decap.apply (fun _  -> ()) (Decap.string "\206\155" "\206\155");
       Decap.apply (fun _  -> ()) (Decap.string "/\\" "/\\")])
let (dot :unit grammar)= Decap.declare_grammar "dot"
let _ =
  Decap.set_grammar dot (Decap.apply (fun _  -> ()) (Decap.string "." "."))
let (mapto :unit grammar)= Decap.declare_grammar "mapto"
let _ =
  Decap.set_grammar mapto
    (Decap.alternatives
       [Decap.apply (fun _  -> ()) (Decap.string "->" "->");
       Decap.apply (fun _  -> ())
         (Decap.string "\226\134\146" "\226\134\146");
       Decap.apply (fun _  -> ())
         (Decap.string "\226\134\166" "\226\134\166")])
let (hole :unit grammar)= Decap.declare_grammar "hole"
let _ =
  Decap.set_grammar hole (Decap.apply (fun _  -> ()) (Decap.string "?" "?"))
let (comma :unit grammar)= Decap.declare_grammar "comma"
let _ =
  Decap.set_grammar comma (Decap.apply (fun _  -> ()) (Decap.string "," ","))
let (subset :unit grammar)= Decap.declare_grammar "subset"
let _ =
  Decap.set_grammar subset
    (Decap.alternatives
       [Decap.apply (fun _  -> ())
          (Decap.string "\226\138\130" "\226\138\130");
       Decap.apply (fun _  -> ())
         (Decap.string "\226\138\134" "\226\138\134");
       Decap.apply (fun _  -> ()) (Decap.string "<" "<")])
type pkind_prio =
  | KFunc
  | KProd
  | KAtom
type pterm_prio =
  | TFunc
  | TSeq
  | TAppl
  | TColo
  | TAtom
let (pkind,pkind__set__grammar) = Decap.grammar_family "pkind"
let kind_list = Decap.declare_grammar "kind_list"
let kind_prod = Decap.declare_grammar "kind_prod"
let sum_item = Decap.declare_grammar "sum_item"
let sum_items = Decap.declare_grammar "sum_items"
let prod_item = Decap.declare_grammar "prod_item"
let prod_items = Decap.declare_grammar "prod_items"
let kind = Decap.declare_grammar "kind"
let kind_def = Decap.declare_grammar "kind_def"
let var = Decap.declare_grammar "var"
let lvar = Decap.declare_grammar "lvar"
let (term,term__set__grammar) = Decap.grammar_family "term"
let pattern = Decap.declare_grammar "pattern"
let case = Decap.declare_grammar "case"
let field = Decap.declare_grammar "field"
let tuple = Decap.declare_grammar "tuple"
let list = Decap.declare_grammar "list"
let _ =
  pkind__set__grammar
    (fun p  ->
       Decap.cache
         (Decap.alternatives
            (let y =
               let y =
                 let y =
                   let y =
                     let y =
                       let y =
                         let y =
                           let y =
                             let y =
                               (Decap.fsequence_position (term TAtom)
                                  (Decap.sequence (Decap.string "." ".")
                                     uident
                                     (fun _  ->
                                        fun s  ->
                                          fun t  ->
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    in_pos _loc
                                                      (PDPrj (t, s)))))
                               ::
                               (let y =
                                  let y =
                                    let y =
                                      let y =
                                        let y = [] in
                                        if p = KFunc
                                        then (pkind KProd) :: y
                                        else y in
                                      if p = KProd
                                      then (pkind KAtom) :: y
                                      else y in
                                    if p = KAtom
                                    then
                                      (Decap.fsequence (Decap.string "(" "(")
                                         (Decap.sequence (pkind KFunc)
                                            (Decap.string ")" ")")
                                            (fun a  -> fun _  -> fun _  -> a)))
                                      :: y
                                    else y in
                                  if p = KAtom
                                  then
                                    (Decap.apply_position
                                       (fun _default_0  ->
                                          fun __loc__start__buf  ->
                                            fun __loc__start__pos  ->
                                              fun __loc__end__buf  ->
                                                fun __loc__end__pos  ->
                                                  let _loc =
                                                    locate __loc__start__buf
                                                      __loc__start__pos
                                                      __loc__end__buf
                                                      __loc__end__pos in
                                                  in_pos _loc PHole) hole)
                                    :: y
                                  else y in
                                if p = KAtom
                                then
                                  (Decap.sequence (pkind KAtom)
                                     (Decap.alternatives
                                        [Decap.fsequence_position with_kw
                                           (Decap.fsequence uident
                                              (Decap.sequence
                                                 (Decap.string "=" "=")
                                                 (pkind KAtom)
                                                 (fun _  ->
                                                    fun b  ->
                                                      fun s  ->
                                                        fun _default_0  ->
                                                          fun
                                                            __loc__start__buf
                                                             ->
                                                            fun
                                                              __loc__start__pos
                                                               ->
                                                              fun
                                                                __loc__end__buf
                                                                 ->
                                                                fun
                                                                  __loc__end__pos
                                                                   ->
                                                                  let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                  fun a  ->
                                                                    in_pos
                                                                    _loc
                                                                    (PWith
                                                                    (a, s, b)))));
                                        Decap.fsequence_position when_kw
                                          (Decap.fsequence (pkind KAtom)
                                             (Decap.sequence subset
                                                (pkind KAtom)
                                                (fun _default_0  ->
                                                   fun c  ->
                                                     fun b  ->
                                                       fun _default_1  ->
                                                         fun
                                                           __loc__start__buf 
                                                           ->
                                                           fun
                                                             __loc__start__pos
                                                              ->
                                                             fun
                                                               __loc__end__buf
                                                                ->
                                                               fun
                                                                 __loc__end__pos
                                                                  ->
                                                                 let _loc =
                                                                   locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                 fun a  ->
                                                                   in_pos
                                                                    _loc
                                                                    (PWhen
                                                                    (a, b, c)))))])
                                     (fun a  -> fun f  -> f a))
                                  :: y
                                else y) in
                             if p = KAtom
                             then
                               (Decap.fsequence_position
                                  (Decap.string "[" "[")
                                  (Decap.sequence sum_items
                                     (Decap.string "]" "]")
                                     (fun fs  ->
                                        fun _  ->
                                          fun _  ->
                                            fun __loc__start__buf  ->
                                              fun __loc__start__pos  ->
                                                fun __loc__end__buf  ->
                                                  fun __loc__end__pos  ->
                                                    let _loc =
                                                      locate
                                                        __loc__start__buf
                                                        __loc__start__pos
                                                        __loc__end__buf
                                                        __loc__end__pos in
                                                    in_pos _loc (PSum fs))))
                               :: y
                             else y in
                           if p = KProd
                           then
                             (Decap.apply_position
                                (fun fs  ->
                                   fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           in_pos _loc (PProd fs)) kind_prod)
                             :: y
                           else y in
                         if p = KAtom
                         then
                           (Decap.fsequence_position (Decap.string "{" "{")
                              (Decap.sequence prod_items
                                 (Decap.string "}" "}")
                                 (fun fs  ->
                                    fun _  ->
                                      fun _  ->
                                        fun __loc__start__buf  ->
                                          fun __loc__start__pos  ->
                                            fun __loc__end__buf  ->
                                              fun __loc__end__pos  ->
                                                let _loc =
                                                  locate __loc__start__buf
                                                    __loc__start__pos
                                                    __loc__end__buf
                                                    __loc__end__pos in
                                                in_pos _loc (PProd fs))))
                           :: y
                         else y in
                       if p = KFunc
                       then
                         (Decap.fsequence_position nu
                            (Decap.sequence uident (pkind KFunc)
                               (fun id  ->
                                  fun a  ->
                                    fun _default_0  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              in_pos _loc (PNu (id, a)))))
                         :: y
                       else y in
                     if p = KFunc
                     then
                       (Decap.fsequence_position mu
                          (Decap.sequence uident (pkind KFunc)
                             (fun id  ->
                                fun a  ->
                                  fun _default_0  ->
                                    fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos in
                                            in_pos _loc (PMu (id, a)))))
                       :: y
                     else y in
                   if p = KFunc
                   then
                     (Decap.fsequence_position exists
                        (Decap.sequence uident (pkind KFunc)
                           (fun id  ->
                              fun a  ->
                                fun _default_0  ->
                                  fun __loc__start__buf  ->
                                    fun __loc__start__pos  ->
                                      fun __loc__end__buf  ->
                                        fun __loc__end__pos  ->
                                          let _loc =
                                            locate __loc__start__buf
                                              __loc__start__pos
                                              __loc__end__buf __loc__end__pos in
                                          in_pos _loc (PExis (id, a)))))
                     :: y
                   else y in
                 if p = KFunc
                 then
                   (Decap.fsequence_position forall
                      (Decap.sequence uident (pkind KFunc)
                         (fun id  ->
                            fun a  ->
                              fun _default_0  ->
                                fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        in_pos _loc (PFAll (id, a)))))
                   :: y
                 else y in
               if p = KAtom
               then
                 (Decap.sequence_position uident
                    (Decap.option []
                       (Decap.fsequence (Decap.string "(" "(")
                          (Decap.sequence kind_list (Decap.string ")" ")")
                             (fun l  -> fun _  -> fun _  -> l))))
                    (fun id  ->
                       fun l  ->
                         fun __loc__start__buf  ->
                           fun __loc__start__pos  ->
                             fun __loc__end__buf  ->
                               fun __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 in_pos _loc (PTVar (id, l))))
                 :: y
               else y in
             if p = KFunc
             then
               (Decap.fsequence_position (pkind KProd)
                  (Decap.sequence arrow (pkind KFunc)
                     (fun _default_0  ->
                        fun b  ->
                          fun a  ->
                            fun __loc__start__buf  ->
                              fun __loc__start__pos  ->
                                fun __loc__end__buf  ->
                                  fun __loc__end__pos  ->
                                    let _loc =
                                      locate __loc__start__buf
                                        __loc__start__pos __loc__end__buf
                                        __loc__end__pos in
                                    in_pos _loc (PFunc (a, b)))))
               :: y
             else y)))
let _ =
  Decap.set_grammar kind_list (Decap.cache (list_sep (pkind KFunc) ","))
let _ =
  Decap.set_grammar kind_prod
    (Decap.cache
       (Decap.apply
          (fun l  ->
             List.mapi (fun i  -> fun x  -> ((string_of_int (i + 1)), x)) l)
          (glist_sep'' (pkind KAtom) time)))
let _ =
  Decap.set_grammar sum_item
    (Decap.cache
       (Decap.sequence uident
          (Decap.option None
             (Decap.apply (fun x  -> Some x)
                (Decap.sequence of_kw (pkind KFunc) (fun _  -> fun a  -> a))))
          (fun id  -> fun a  -> (id, a))))
let _ = Decap.set_grammar sum_items (Decap.cache (list_sep sum_item "|"))
let _ =
  Decap.set_grammar prod_item
    (Decap.cache
       (Decap.fsequence lident
          (Decap.sequence (Decap.string ":" ":") (pkind KFunc)
             (fun _  -> fun a  -> fun id  -> (id, a)))))
let _ = Decap.set_grammar prod_items (Decap.cache (list_sep prod_item ";"))
let _ = Decap.set_grammar kind (Decap.cache (pkind KFunc))
let _ =
  Decap.set_grammar kind_def
    (Decap.cache
       (Decap.fsequence uident
          (Decap.fsequence
             (Decap.option []
                (Decap.fsequence (Decap.string "(" "(")
                   (Decap.sequence (list_sep' uident ",")
                      (Decap.string ")" ")")
                      (fun ids  -> fun _  -> fun _  -> ids))))
             (Decap.sequence (Decap.string "=" "=") kind
                (fun _  -> fun k  -> fun args  -> fun id  -> (id, args, k))))))
let _ =
  Decap.set_grammar var
    (Decap.cache
       (Decap.alternatives
          [Decap.apply
             (fun id  -> let (_loc_id,id) = id in ((in_pos _loc_id id), None))
             (Decap.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x)) lident);
          Decap.fsequence (Decap.string "(" "(")
            (Decap.fsequence
               (Decap.apply_position
                  (fun x  ->
                     fun str  ->
                       fun pos  ->
                         fun str'  ->
                           fun pos'  -> ((locate str pos str' pos'), x))
                  lident)
               (Decap.fsequence (Decap.string ":" ":")
                  (Decap.sequence kind (Decap.string ")" ")")
                     (fun k  ->
                        fun _  ->
                          fun _  ->
                            fun id  ->
                              let (_loc_id,id) = id in
                              fun _  -> ((in_pos _loc_id id), (Some k))))))]))
let _ =
  Decap.set_grammar lvar
    (Decap.cache
       (Decap.alternatives
          [Decap.apply
             (fun id  -> let (_loc_id,id) = id in ((in_pos _loc_id id), None))
             (Decap.apply_position
                (fun x  ->
                   fun str  ->
                     fun pos  ->
                       fun str'  ->
                         fun pos'  -> ((locate str pos str' pos'), x)) lident);
          Decap.fsequence
            (Decap.apply_position
               (fun x  ->
                  fun str  ->
                    fun pos  ->
                      fun str'  ->
                        fun pos'  -> ((locate str pos str' pos'), x)) lident)
            (Decap.sequence (Decap.string ":" ":") kind
               (fun _  ->
                  fun k  ->
                    fun id  ->
                      let (_loc_id,id) = id in
                      ((in_pos _loc_id id), (Some k))))]))
let _ =
  term__set__grammar
    (fun p  ->
       Decap.cache
         (Decap.alternatives
            (let y =
               let y =
                 let y =
                   let y =
                     let y =
                       let y =
                         let y =
                           let y =
                             let y =
                               let y =
                                 let y =
                                   let y =
                                     let y =
                                       let y =
                                         (Decap.fsequence
                                            (Decap.string "[" "[")
                                            (Decap.sequence list
                                               (Decap.string "]" "]")
                                               (fun l  ->
                                                  fun _  -> fun _  -> l)))
                                         ::
                                         (let y =
                                            (Decap.fsequence_position if_kw
                                               (Decap.fsequence (term TFunc)
                                                  (Decap.fsequence then_kw
                                                     (Decap.fsequence
                                                        (term TFunc)
                                                        (Decap.sequence
                                                           else_kw
                                                           (term TFunc)
                                                           (fun _default_0 
                                                              ->
                                                              fun e  ->
                                                                fun t  ->
                                                                  fun
                                                                    _default_1
                                                                     ->
                                                                    fun c  ->
                                                                    fun
                                                                    _default_2
                                                                     ->
                                                                    fun
                                                                    __loc__start__buf
                                                                     ->
                                                                    fun
                                                                    __loc__start__pos
                                                                     ->
                                                                    fun
                                                                    __loc__end__buf
                                                                     ->
                                                                    fun
                                                                    __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    in_pos
                                                                    _loc
                                                                    (PCase
                                                                    (c,
                                                                    [
                                                                    ("Tru",
                                                                    None, t);
                                                                    ("Fls",
                                                                    None, e)]))))))))
                                            ::
                                            (let y =
                                               let y =
                                                 let y =
                                                   let y = [] in
                                                   if p = TFunc
                                                   then (term TSeq) :: y
                                                   else y in
                                                 if p = TSeq
                                                 then
                                                   (Decap.sequence_position
                                                      (term TAppl)
                                                      (Decap.option None
                                                         (Decap.apply
                                                            (fun x  -> Some x)
                                                            (Decap.sequence
                                                               (Decap.string
                                                                  "::" "::")
                                                               (term TSeq)
                                                               (fun _  ->
                                                                  fun l  -> l))))
                                                      (fun t  ->
                                                         fun l  ->
                                                           fun
                                                             __loc__start__buf
                                                              ->
                                                             fun
                                                               __loc__start__pos
                                                                ->
                                                               fun
                                                                 __loc__end__buf
                                                                  ->
                                                                 fun
                                                                   __loc__end__pos
                                                                    ->
                                                                   let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                   match l
                                                                   with
                                                                   | 
                                                                   None  -> t
                                                                   | 
                                                                   Some l ->
                                                                    list_cons
                                                                    _loc t l))
                                                   :: y
                                                 else y in
                                               if p = TAppl
                                               then (term TColo) :: y
                                               else y in
                                             if p = TColo
                                             then (term TAtom) :: y
                                             else y) in
                                          if p = TFunc
                                          then
                                            (Decap.fsequence_position let_kw
                                               (Decap.fsequence
                                                  (Decap.option None
                                                     (Decap.apply
                                                        (fun x  -> Some x)
                                                        rec_kw))
                                                  (Decap.fsequence lvar
                                                     (Decap.fsequence
                                                        (Decap.string "=" "=")
                                                        (Decap.fsequence
                                                           (Decap.apply_position
                                                              (fun x  ->
                                                                 fun str  ->
                                                                   fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                              (term TFunc))
                                                           (Decap.sequence
                                                              in_kw
                                                              (Decap.apply_position
                                                                 (fun x  ->
                                                                    fun str 
                                                                    ->
                                                                    fun pos 
                                                                    ->
                                                                    fun str' 
                                                                    ->
                                                                    fun pos' 
                                                                    ->
                                                                    ((locate
                                                                    str pos
                                                                    str' pos'),
                                                                    x))
                                                                 (term TFunc))
                                                              (fun _default_0
                                                                  ->
                                                                 fun u  ->
                                                                   let 
                                                                    (_loc_u,u)
                                                                    = u in
                                                                   fun t  ->
                                                                    let 
                                                                    (_loc_t,t)
                                                                    = t in
                                                                    fun _  ->
                                                                    fun id 
                                                                    ->
                                                                    fun r  ->
                                                                    fun
                                                                    _default_1
                                                                     ->
                                                                    fun
                                                                    __loc__start__buf
                                                                     ->
                                                                    fun
                                                                    __loc__start__pos
                                                                     ->
                                                                    fun
                                                                    __loc__end__buf
                                                                     ->
                                                                    fun
                                                                    __loc__end__pos
                                                                     ->
                                                                    let _loc
                                                                    =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                    let t =
                                                                    if
                                                                    r = None
                                                                    then t
                                                                    else
                                                                    in_pos
                                                                    _loc_t
                                                                    (PFixY
                                                                    (id, t)) in
                                                                    in_pos
                                                                    _loc
                                                                    (PAppl
                                                                    ((in_pos
                                                                    _loc_u
                                                                    (PLAbs
                                                                    ([id], u))),
                                                                    t)))))))))
                                            :: y
                                          else y) in
                                       if p = TFunc
                                       then
                                         (Decap.fsequence_position fix_kw
                                            (Decap.fsequence var
                                               (Decap.sequence dot
                                                  (term TFunc)
                                                  (fun _default_0  ->
                                                     fun u  ->
                                                       fun x  ->
                                                         fun _default_1  ->
                                                           fun
                                                             __loc__start__buf
                                                              ->
                                                             fun
                                                               __loc__start__pos
                                                                ->
                                                               fun
                                                                 __loc__end__buf
                                                                  ->
                                                                 fun
                                                                   __loc__end__pos
                                                                    ->
                                                                   let _loc =
                                                                    locate
                                                                    __loc__start__buf
                                                                    __loc__start__pos
                                                                    __loc__end__buf
                                                                    __loc__end__pos in
                                                                   in_pos
                                                                    _loc
                                                                    (PFixY
                                                                    (x, u))))))
                                         :: y
                                       else y in
                                     if p = TAtom
                                     then
                                       (Decap.apply_position
                                          (fun id  ->
                                             fun __loc__start__buf  ->
                                               fun __loc__start__pos  ->
                                                 fun __loc__end__buf  ->
                                                   fun __loc__end__pos  ->
                                                     let _loc =
                                                       locate
                                                         __loc__start__buf
                                                         __loc__start__pos
                                                         __loc__end__buf
                                                         __loc__end__pos in
                                                     in_pos _loc (PLVar id))
                                          lident)
                                       :: y
                                     else y in
                                   if p = TColo
                                   then
                                     (Decap.fsequence_position (term TColo)
                                        (Decap.sequence
                                           (Decap.string ":" ":") kind
                                           (fun _  ->
                                              fun k  ->
                                                fun t  ->
                                                  fun __loc__start__buf  ->
                                                    fun __loc__start__pos  ->
                                                      fun __loc__end__buf  ->
                                                        fun __loc__end__pos 
                                                          ->
                                                          let _loc =
                                                            locate
                                                              __loc__start__buf
                                                              __loc__start__pos
                                                              __loc__end__buf
                                                              __loc__end__pos in
                                                          in_pos _loc
                                                            (PCoer (t, k)))))
                                     :: y
                                   else y in
                                 if p = TAtom
                                 then
                                   (Decap.fsequence_position
                                      (Decap.string "(" "(")
                                      (Decap.sequence tuple
                                         (Decap.string ")" ")")
                                         (fun fs  ->
                                            fun _  ->
                                              fun _  ->
                                                fun __loc__start__buf  ->
                                                  fun __loc__start__pos  ->
                                                    fun __loc__end__buf  ->
                                                      fun __loc__end__pos  ->
                                                        let _loc =
                                                          locate
                                                            __loc__start__buf
                                                            __loc__start__pos
                                                            __loc__end__buf
                                                            __loc__end__pos in
                                                        match fs with
                                                        | [] -> assert false
                                                        | (_,t)::[] -> t
                                                        | _ ->
                                                            in_pos _loc
                                                              (PReco fs))))
                                   :: y
                                 else y in
                               if p = TAtom
                               then
                                 (Decap.fsequence_position
                                    (Decap.string "{" "{")
                                    (Decap.fsequence (list_sep field ";")
                                       (Decap.sequence
                                          (Decap.option None
                                             (Decap.apply (fun x  -> Some x)
                                                (Decap.string ";" ";")))
                                          (Decap.string "}" "}")
                                          (fun _default_0  ->
                                             fun _  ->
                                               fun fs  ->
                                                 fun _  ->
                                                   fun __loc__start__buf  ->
                                                     fun __loc__start__pos 
                                                       ->
                                                       fun __loc__end__buf 
                                                         ->
                                                         fun __loc__end__pos 
                                                           ->
                                                           let _loc =
                                                             locate
                                                               __loc__start__buf
                                                               __loc__start__pos
                                                               __loc__end__buf
                                                               __loc__end__pos in
                                                           in_pos _loc
                                                             (PReco fs)))))
                                 :: y
                               else y in
                             if p = TFunc
                             then
                               (Decap.fsequence_position case_kw
                                  (Decap.fsequence (term TFunc)
                                     (Decap.fsequence of_kw
                                        (Decap.sequence
                                           (Decap.option None
                                              (Decap.apply (fun x  -> Some x)
                                                 (Decap.string "|" "|")))
                                           (list_sep case "|")
                                           (fun _default_0  ->
                                              fun ps  ->
                                                fun _default_1  ->
                                                  fun t  ->
                                                    fun _default_2  ->
                                                      fun __loc__start__buf 
                                                        ->
                                                        fun __loc__start__pos
                                                           ->
                                                          fun __loc__end__buf
                                                             ->
                                                            fun
                                                              __loc__end__pos
                                                               ->
                                                              let _loc =
                                                                locate
                                                                  __loc__start__buf
                                                                  __loc__start__pos
                                                                  __loc__end__buf
                                                                  __loc__end__pos in
                                                              in_pos _loc
                                                                (PCase
                                                                   (t, ps)))))))
                               :: y
                             else y in
                           if p = TAtom
                           then
                             (Decap.fsequence_position (term TAtom)
                                (Decap.sequence (Decap.string "." ".") lident
                                   (fun _  ->
                                      fun l  ->
                                        fun t  ->
                                          fun __loc__start__buf  ->
                                            fun __loc__start__pos  ->
                                              fun __loc__end__buf  ->
                                                fun __loc__end__pos  ->
                                                  let _loc =
                                                    locate __loc__start__buf
                                                      __loc__start__pos
                                                      __loc__end__buf
                                                      __loc__end__pos in
                                                  in_pos _loc (PProj (t, l)))))
                             :: y
                           else y in
                         if p = TAtom
                         then
                           (Decap.sequence_position uident
                              (Decap.option None
                                 (Decap.apply (fun x  -> Some x) (term TAtom)))
                              (fun c  ->
                                 fun uo  ->
                                   fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           in_pos _loc (PCstr (c, uo))))
                           :: y
                         else y in
                       if p = TAtom
                       then
                         (Decap.fsequence_position
                            (Decap.ignore_next_blank
                               (Decap.string "print(" "print("))
                            (Decap.sequence
                               (Decap.ignore_next_blank string_lit)
                               (Decap.string ")" ")")
                               (fun s  ->
                                  fun _  ->
                                    fun _  ->
                                      fun __loc__start__buf  ->
                                        fun __loc__start__pos  ->
                                          fun __loc__end__buf  ->
                                            fun __loc__end__pos  ->
                                              let _loc =
                                                locate __loc__start__buf
                                                  __loc__start__pos
                                                  __loc__end__buf
                                                  __loc__end__pos in
                                              in_pos _loc (PPrnt s))))
                         :: y
                       else y in
                     if p = TSeq
                     then
                       (Decap.fsequence_position (term TAppl)
                          (Decap.sequence (Decap.string ";" ";") (term TSeq)
                             (fun _  ->
                                fun u  ->
                                  fun t  ->
                                    fun __loc__start__buf  ->
                                      fun __loc__start__pos  ->
                                        fun __loc__end__buf  ->
                                          fun __loc__end__pos  ->
                                            let _loc =
                                              locate __loc__start__buf
                                                __loc__start__pos
                                                __loc__end__buf
                                                __loc__end__pos in
                                            sequence _loc t u)))
                       :: y
                     else y in
                   if p = TAppl
                   then
                     (Decap.sequence_position (term TAppl) (term TColo)
                        (fun t  ->
                           fun u  ->
                             fun __loc__start__buf  ->
                               fun __loc__start__pos  ->
                                 fun __loc__end__buf  ->
                                   fun __loc__end__pos  ->
                                     let _loc =
                                       locate __loc__start__buf
                                         __loc__start__pos __loc__end__buf
                                         __loc__end__pos in
                                     in_pos _loc (PAppl (t, u))))
                     :: y
                   else y in
                 if p = TFunc
                 then
                   (Decap.fsequence_position klam
                      (Decap.sequence
                         (Decap.apply_position
                            (fun x  ->
                               fun str  ->
                                 fun pos  ->
                                   fun str'  ->
                                     fun pos'  ->
                                       ((locate str pos str' pos'), x))
                            uident) (term TFunc)
                         (fun x  ->
                            let (_loc_x,x) = x in
                            fun t  ->
                              fun _default_0  ->
                                fun __loc__start__buf  ->
                                  fun __loc__start__pos  ->
                                    fun __loc__end__buf  ->
                                      fun __loc__end__pos  ->
                                        let _loc =
                                          locate __loc__start__buf
                                            __loc__start__pos __loc__end__buf
                                            __loc__end__pos in
                                        in_pos _loc
                                          (PKAbs ((in_pos _loc_x x), t)))))
                   :: y
                 else y in
               if p = TFunc
               then
                 (Decap.fsequence_position fun_kw
                    (Decap.fsequence
                       (Decap.apply List.rev
                          (Decap.fixpoint1 []
                             (Decap.apply (fun x  -> fun l  -> x :: l) var)))
                       (Decap.sequence mapto (term TFunc)
                          (fun _default_0  ->
                             fun t  ->
                               fun xs  ->
                                 fun _default_1  ->
                                   fun __loc__start__buf  ->
                                     fun __loc__start__pos  ->
                                       fun __loc__end__buf  ->
                                         fun __loc__end__pos  ->
                                           let _loc =
                                             locate __loc__start__buf
                                               __loc__start__pos
                                               __loc__end__buf
                                               __loc__end__pos in
                                           in_pos _loc (PLAbs (xs, t))))))
                 :: y
               else y in
             if p = TFunc
             then
               (Decap.fsequence_position lambda
                  (Decap.fsequence
                     (Decap.apply List.rev
                        (Decap.fixpoint1 []
                           (Decap.apply (fun x  -> fun l  -> x :: l) var)))
                     (Decap.sequence dot (term TFunc)
                        (fun _default_0  ->
                           fun t  ->
                             fun xs  ->
                               fun _default_1  ->
                                 fun __loc__start__buf  ->
                                   fun __loc__start__pos  ->
                                     fun __loc__end__buf  ->
                                       fun __loc__end__pos  ->
                                         let _loc =
                                           locate __loc__start__buf
                                             __loc__start__pos
                                             __loc__end__buf __loc__end__pos in
                                         in_pos _loc (PLAbs (xs, t))))))
               :: y
             else y)))
let _ =
  Decap.set_grammar pattern
    (Decap.cache
       (Decap.alternatives
          [Decap.sequence uident
             (Decap.option None (Decap.apply (fun x  -> Some x) var))
             (fun c  -> fun x  -> (c, x));
          Decap.sequence (Decap.string "[" "[") (Decap.string "]" "]")
            (fun _  -> fun _  -> ("Nil", None))]))
let _ =
  Decap.set_grammar case
    (Decap.cache
       (Decap.fsequence pattern
          (Decap.sequence arrow (term TFunc)
             (fun _  -> fun t  -> fun ((c,x) as _default_0)  -> (c, x, t)))))
let _ =
  Decap.set_grammar field
    (Decap.cache
       (Decap.fsequence_position lident
          (Decap.fsequence
             (Decap.option None
                (Decap.apply (fun x  -> Some x)
                   (Decap.sequence (Decap.string ":" ":") kind
                      (fun _  -> fun _default_0  -> _default_0))))
             (Decap.sequence (Decap.string "=" "=") (term TFunc)
                (fun _  ->
                   fun t  ->
                     fun k  ->
                       fun l  ->
                         fun __loc__start__buf  ->
                           fun __loc__start__pos  ->
                             fun __loc__end__buf  ->
                               fun __loc__end__pos  ->
                                 let _loc =
                                   locate __loc__start__buf __loc__start__pos
                                     __loc__end__buf __loc__end__pos in
                                 (l,
                                   (match k with
                                    | None  -> t
                                    | Some k -> in_pos _loc (PCoer (t, k)))))))))
let _ =
  Decap.set_grammar tuple
    (Decap.cache
       (Decap.apply
          (fun l  ->
             List.mapi (fun i  -> fun x  -> ((string_of_int (i + 1)), x)) l)
          (glist_sep' (term TFunc) comma)))
let _ =
  Decap.set_grammar list
    (Decap.cache
       (Decap.alternatives
          [Decap.apply_position
             (fun _  ->
                fun __loc__start__buf  ->
                  fun __loc__start__pos  ->
                    fun __loc__end__buf  ->
                      fun __loc__end__pos  ->
                        let _loc =
                          locate __loc__start__buf __loc__start__pos
                            __loc__end__buf __loc__end__pos in
                        list_nil _loc) (Decap.empty ());
          Decap.fsequence_position (term TFunc)
            (Decap.sequence (Decap.string "," ",") list
               (fun _  ->
                  fun l  ->
                    fun t  ->
                      fun __loc__start__buf  ->
                        fun __loc__start__pos  ->
                          fun __loc__end__buf  ->
                            fun __loc__end__pos  ->
                              let _loc =
                                locate __loc__start__buf __loc__start__pos
                                  __loc__end__buf __loc__end__pos in
                              list_cons _loc t l))]))
let term = term TFunc
exception Finish
let comment_char =
  black_box
    (fun str  ->
       fun pos  ->
         let (c,str',pos') = Input.read str pos in
         match c with
         | '\255' -> give_up "Unclosed comment."
         | '*' ->
             let (c',_,_) = Input.read str' pos' in
             if c' = ')'
             then give_up "Not the place to close a comment."
             else ((), str', pos')
         | _ -> ((), str', pos')) Charset.full_charset None "ANY"
let blank_chars =
  let open Charset in
    List.fold_left add empty_charset [' '; '\n'; '\r'; '\t']
let comment = Decap.declare_grammar "comment"
let _ =
  Decap.set_grammar comment
    (Decap.fsequence (Decap.string "(*" "(*")
       (Decap.sequence
          (Decap.apply List.rev
             (Decap.fixpoint' []
                (Decap.apply (fun x  -> fun l  -> x :: l) comment_char)))
          (Decap.string "*)" "*)") (fun _  -> fun _  -> fun _  -> ())))
let blank_parser = Decap.declare_grammar "blank_parser"
let _ =
  Decap.set_grammar blank_parser
    (Decap.apply (fun _  -> ())
       (Decap.apply List.rev
          (Decap.fixpoint' []
             (Decap.apply (fun x  -> fun l  -> x :: l)
                (Decap.alternatives
                   [Decap.apply (fun _  -> ()) comment;
                   Decap.apply (fun _  -> ()) (in_charset blank_chars)])))))
let blank = blank_grammar blank_parser no_blank
let enabled = Decap.declare_grammar "enabled"
let _ =
  Decap.set_grammar enabled
    (Decap.alternatives
       [Decap.apply (fun _  -> true) (Decap.string "on" "on");
       Decap.apply (fun _  -> false) (Decap.string "off" "off")])
let latex_ch = ref stdout
let open_latex fn =
  if (!latex_ch) <> stdout then close_out (!latex_ch);
  latex_ch := (open_out fn)
let opt_flag = Decap.declare_grammar "opt_flag"
let _ =
  Decap.set_grammar opt_flag
    (Decap.alternatives
       [Decap.sequence (Decap.string "verbose" "verbose") enabled
          (fun _  -> fun b  -> verbose := b);
       Decap.sequence (Decap.string "texfile" "texfile") string_lit
         (fun _  -> fun fn  -> open_latex fn);
       Decap.sequence
         (Decap.string "print_term_in_subtyping" "print_term_in_subtyping")
         enabled (fun _  -> fun b  -> Print.print_term_in_subtyping := b)])
let read_file = ref (fun _  -> assert false)
let latex_atom = Decap.declare_grammar "latex_atom"
let latex_text = Decap.declare_grammar "latex_text"
let _ =
  Decap.set_grammar latex_atom
    (Decap.alternatives
       [Decap.fsequence (Decap.string "#" "#")
          (Decap.sequence (Decap.string "witnesses" "witnesses")
             (Decap.string "#" "#")
             (fun _  -> fun _  -> fun _  -> Latex_trace.Witnesses));
       Decap.fsequence (Decap.string "#" "#")
         (Decap.fsequence (Decap.option 0 int_lit)
            (Decap.fsequence
               (Decap.option None
                  (Decap.apply (fun x  -> Some x) (Decap.string "!" "!")))
               (Decap.sequence kind (Decap.string "#" "#")
                  (fun k  ->
                     fun _  ->
                       fun u  ->
                         fun br  ->
                           fun _  ->
                             Latex_trace.Kind
                               (br, (u <> None),
                                 (unbox (unsugar_kind [] [] k)))))));
       Decap.fsequence (Decap.string "@" "@")
         (Decap.fsequence (Decap.option 0 int_lit)
            (Decap.fsequence
               (Decap.option None
                  (Decap.apply (fun x  -> Some x) (Decap.string "!" "!")))
               (Decap.sequence term (Decap.string "@" "@")
                  (fun t  ->
                     fun _  ->
                       fun u  ->
                         fun br  ->
                           fun _  ->
                             Latex_trace.Term
                               (br, (u <> None),
                                 (unbox (unsugar_term [] [] t)))))));
       Decap.apply (fun t  -> Latex_trace.Text (string_of_chars t))
         (Decap.apply List.rev
            (Decap.fixpoint1 []
               (Decap.apply (fun x  -> fun l  -> x :: l)
                  (in_charset
                     (let open Charset in
                        List.fold_left del full_charset ['}'; '{'; '@'; '#'])))));
       latex_text;
       Decap.fsequence (Decap.string "#" "#")
         (Decap.fsequence (Decap.string "check" "check")
            (Decap.fsequence kind
               (Decap.fsequence subset
                  (Decap.sequence kind (Decap.string "#" "#")
                     (fun b  ->
                        fun _  ->
                          fun _default_0  ->
                            fun a  ->
                              fun _  ->
                                fun _  ->
                                  let a = unbox (unsugar_kind [] [] a) in
                                  let b = unbox (unsugar_kind [] [] b) in
                                  generic_subtype a b;
                                  (let prf = collect_subtyping_proof () in
                                   Latex_trace.SProof prf))))));
       Decap.fsequence (Decap.string "#" "#")
         (Decap.fsequence (Decap.option 0 int_lit)
            (Decap.fsequence (Decap.string ":" ":")
               (Decap.sequence lident (Decap.string "#" "#")
                  (fun id  ->
                     fun _  ->
                       fun _  ->
                         fun br  ->
                           fun _  ->
                             let t = Hashtbl.find val_env id in
                             Latex_trace.Kind (br, false, (t.ttype))))));
       Decap.fsequence (Decap.string "#" "#")
         (Decap.fsequence (Decap.option 0 int_lit)
            (Decap.fsequence (Decap.string "?" "?")
               (Decap.sequence uident (Decap.string "#" "#")
                  (fun id  ->
                     fun _  ->
                       fun _  ->
                         fun br  ->
                           fun _  ->
                             let t = Hashtbl.find typ_env id in
                             Latex_trace.KindDef (br, t)))));
       Decap.fsequence (Decap.string "##" "##")
         (Decap.sequence lident (Decap.string "#" "#")
            (fun id  ->
               fun _  ->
                 fun _  ->
                   let t = Hashtbl.find val_env id in
                   Latex_trace.TProof (t.proof)))])
let _ =
  Decap.set_grammar latex_text
    (Decap.fsequence (Decap.string "{" "{")
       (Decap.sequence
          (Decap.apply List.rev
             (Decap.fixpoint []
                (Decap.apply (fun x  -> fun l  -> x :: l) latex_atom)))
          (Decap.string "}" "}")
          (fun l  -> fun _  -> fun _  -> Latex_trace.List l)))
let latex_name_aux = Decap.declare_grammar "latex_name_aux"
let latex_name = Decap.declare_grammar "latex_name"
let _ =
  Decap.set_grammar latex_name_aux
    (Decap.alternatives
       [Decap.apply (fun t  -> Latex_trace.Text (string_of_chars t))
          (Decap.apply List.rev
             (Decap.fixpoint1 []
                (Decap.apply (fun x  -> fun l  -> x :: l)
                   (in_charset
                      (let open Charset in
                         List.fold_left del full_charset ['}'; '{'; '@'; '#'])))));
       Decap.fsequence (Decap.string "{" "{")
         (Decap.sequence
            (Decap.apply List.rev
               (Decap.fixpoint []
                  (Decap.apply (fun x  -> fun l  -> x :: l) latex_name_aux)))
            (Decap.string "}" "}")
            (fun l  -> fun _  -> fun _  -> Latex_trace.List l))])
let _ =
  Decap.set_grammar latex_name
    (Decap.fsequence (Decap.string "{" "{")
       (Decap.sequence
          (Decap.apply List.rev
             (Decap.fixpoint []
                (Decap.apply (fun x  -> fun l  -> x :: l) latex_name_aux)))
          (Decap.string "}" "}")
          (fun t  ->
             fun _  -> fun _  -> Latex_trace.to_string (Latex_trace.List t))))
let ignore_latex = ref false
let command = Decap.declare_grammar "command"
let _ =
  Decap.set_grammar command
    (Decap.alternatives
       [Decap.fsequence type_kw
          (Decap.sequence
             (Decap.option None (Decap.apply (fun x  -> Some x) latex_name))
             kind_def
             (fun tex  ->
                fun ((name,args,k) as _default_0)  ->
                  fun _default_1  ->
                    let arg_names = Array.of_list args in
                    let f args =
                      let env = ref [] in
                      Array.iteri
                        (fun i  ->
                           fun k  -> env := (((arg_names.(i)), k) :: (!env)))
                        args;
                      unsugar_kind [] (!env) k in
                    let b = mbind mk_free_tvar arg_names f in
                    let td =
                      {
                        tdef_name = name;
                        tdef_tex_name =
                          (match tex with
                           | None  -> "\\mathrm{" ^ (name ^ "}")
                           | Some s -> s);
                        tdef_arity = (Array.length arg_names);
                        tdef_value = (unbox b)
                      } in
                    Printf.fprintf stdout "%a\n%!" (print_kind_def false) td;
                    Hashtbl.add typ_env name td));
       Decap.sequence unfold_kw kind
         (fun _default_0  ->
            fun k  ->
              let k = unbox (unsugar_kind [] [] k) in
              Printf.fprintf stdout "%a\n%!" (print_kind true) k);
       Decap.sequence parse_kw term
         (fun _default_0  ->
            fun t  ->
              let t = unbox (unsugar_term [] [] t) in
              Printf.fprintf stdout "%a\n%!" (print_term false) t);
       Decap.sequence eval_kw term
         (fun _default_0  ->
            fun t  ->
              let t = unbox (unsugar_term [] [] t) in
              let t = eval t in
              Printf.fprintf stdout "%a\n%!" (print_term false) t);
       Decap.fsequence val_kw
         (Decap.fsequence
            (Decap.option None (Decap.apply (fun x  -> Some x) rec_kw))
            (Decap.fsequence
               (Decap.option None (Decap.apply (fun x  -> Some x) latex_name))
               (Decap.fsequence
                  (Decap.apply_position
                     (fun x  ->
                        fun str  ->
                          fun pos  ->
                            fun str'  ->
                              fun pos'  -> ((locate str pos str' pos'), x))
                     lident)
                  (Decap.fsequence (Decap.string ":" ":")
                     (Decap.fsequence kind
                        (Decap.sequence (Decap.string "=" "=")
                           (Decap.apply_position
                              (fun x  ->
                                 fun str  ->
                                   fun pos  ->
                                     fun str'  ->
                                       fun pos'  ->
                                         ((locate str pos str' pos'), x))
                              term)
                           (fun _  ->
                              fun t  ->
                                let (_loc_t,t) = t in
                                fun k  ->
                                  fun _  ->
                                    fun id  ->
                                      let (_loc_id,id) = id in
                                      fun tex  ->
                                        fun r  ->
                                          fun _default_0  ->
                                            let t =
                                              if r = None
                                              then t
                                              else
                                                in_pos _loc_t
                                                  (PFixY
                                                     (((in_pos _loc_id id),
                                                        (Some k)), t)) in
                                            let t =
                                              unbox (unsugar_term [] [] t) in
                                            let k =
                                              unbox (unsugar_kind [] [] k) in
                                            let prf =
                                              try
                                                type_check t k;
                                                (let prf =
                                                   collect_typing_proof () in
                                                 if !verbose
                                                 then print_typing_proof prf;
                                                 prf)
                                              with
                                              | e ->
                                                  (trace_backtrace ();
                                                   raise e) in
                                            reset_all ();
                                            (let tn = eval t in
                                             Hashtbl.add val_env id
                                               {
                                                 name = id;
                                                 tex_name =
                                                   (match tex with
                                                    | None  ->
                                                        "\\mathrm{" ^
                                                          (id ^ "}")
                                                    | Some s -> s);
                                                 value = tn;
                                                 orig_value = t;
                                                 ttype = k;
                                                 proof = prf
                                               };
                                             Printf.fprintf stdout
                                               "%s : %a\n%!" id
                                               (print_kind false) k))))))));
       Decap.fsequence check_kw
         (Decap.fsequence
            (Decap.option true
               (Decap.apply (fun _  -> false) (Decap.string "not" "not")))
            (Decap.fsequence kind
               (Decap.sequence
                  (Decap.alternatives
                     [Decap.apply (fun _  -> ())
                        (Decap.string "\226\138\130" "\226\138\130");
                     Decap.apply (fun _  -> ())
                       (Decap.string "\226\138\134" "\226\138\134");
                     Decap.apply (fun _  -> ()) (Decap.string "<" "<")]) kind
                  (fun _default_0  ->
                     fun b  ->
                       fun a  ->
                         fun n  ->
                           fun _default_1  ->
                             let a = unbox (unsugar_kind [] [] a) in
                             let b = unbox (unsugar_kind [] [] b) in
                             try
                               generic_subtype a b;
                               (let prf = collect_subtyping_proof () in
                                if (!verbose) || (not n)
                                then
                                  (Printf.eprintf "MUST FAIL\n%!";
                                   print_subtyping_proof prf;
                                   exit 1);
                                reset_epsilon_tbls ();
                                Printf.eprintf "check: OK\n%!")
                             with
                             | Subtype_error s when n ->
                                 (Printf.eprintf "CHECK FAILED: OK %s\n%!" s;
                                  exit 1)
                             | Subtype_error s ->
                                 (Printf.eprintf "check not: OK %s\n%!" s;
                                  trace_state := [];
                                  reset_epsilon_tbls ())
                             | e ->
                                 (Printf.eprintf "UNCAUGHT EXCEPTION: %s\n%!"
                                    (Printexc.to_string e);
                                  exit 1)))));
       Decap.sequence latex_kw latex_text
         (fun _default_0  ->
            fun t  ->
              if not (!ignore_latex) then Latex_trace.output (!latex_ch) t);
       Decap.sequence include_kw string_lit
         (fun _  ->
            fun fn  ->
              let save = !ignore_latex in
              ignore_latex := true; (!read_file) fn; ignore_latex := save);
       Decap.sequence set_kw opt_flag (fun _  -> fun f  -> f)])
let toplevel = Decap.declare_grammar "toplevel"
let _ =
  Decap.set_grammar toplevel
    (Decap.alternatives
       [command;
       Decap.apply (fun _default_0  -> ignore (Sys.command "clear")) clear_kw;
       Decap.apply (fun _default_0  -> raise Finish)
         (Decap.alternatives [quit_kw; exit_kw])])
let toplevel_of_string: string -> unit =
  fun s  -> parse_string toplevel blank s
let file_contents = Decap.declare_grammar "file_contents"
let _ =
  Decap.set_grammar file_contents
    (Decap.apply (fun cs  -> ())
       (Decap.apply List.rev
          (Decap.fixpoint' []
             (Decap.apply (fun x  -> fun l  -> x :: l) command))))
let eval_file fn =
  Printf.printf "## Loading file %S\n%!" fn;
  parse_file file_contents blank fn;
  Printf.printf "## file Loaded %S\n%!" fn
let _ = read_file := eval_file
