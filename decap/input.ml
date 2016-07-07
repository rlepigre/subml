(*
  ======================================================================
  Copyright Christophe Raffalli & Rodolphe Lepigre
  LAMA, UMR 5127 - Université Savoie Mont Blanc

  christophe.raffalli@univ-savoie.fr
  rodolphe.lepigre@univ-savoie.fr

  This software contains implements a parser combinator library together
  with a syntax extension mechanism for the OCaml language.  It  can  be
  used to write parsers using a BNF-like format through a syntax extens-
  ion called pa_parser.

  This software is governed by the CeCILL-B license under French law and
  abiding by the rules of distribution of free software.  You  can  use,
  modify and/or redistribute it under the terms of the CeCILL-B  license
  as circulated by CEA, CNRS and INRIA at the following URL:

            http://www.cecill.info

  The exercising of this freedom is conditional upon a strong obligation
  of giving credits for everybody that distributes a software incorpora-
  ting a software ruled by the current license so as  all  contributions
  to be properly identified and acknowledged.

  As a counterpart to the access to the source code and rights to  copy,
  modify and redistribute granted by the  license,  users  are  provided
  only with a limited warranty and the software's author, the holder  of
  the economic rights, and the successive licensors  have  only  limited
  liability.

  In this respect, the user's attention is drawn to the risks associated
  with loading, using, modifying and/or developing  or  reproducing  the
  software by the user in light of its specific status of free software,
  that may mean that it is complicated  to  manipulate,  and  that  also
  therefore means that it is reserved  for  developers  and  experienced
  professionals having in-depth computer knowledge. Users are  therefore
  encouraged to load and test  the  software's  suitability  as  regards
  their requirements in conditions enabling the security of  their  sys-
  tems and/or data to be ensured and, more generally, to use and operate
  it in the same conditions as regards security.

  The fact that you are presently reading this means that you  have  had
  knowledge of the CeCILL-B license and that you accept its terms.
  ======================================================================
*)

type buffer = buffer_aux Lazy.t
and  buffer_aux =
  { is_empty     : bool     (* Is the buffer empty? *)
  ; name         : string   (* The name of the buffer. *)
  ; lnum         : int      (* Current line number. *)
  ; bol          : int      (* Offset to current line. *)
  ; length       : int      (* Length of the current line. *)
  ; contents     : string   (* Contents of the line. *)
  ; mutable next : buffer   (* Rest of the buffer. *)
  ; ident        : int }    (* Unique identifier for comparison *)

let rec read (lazy b as b0) i =
  if b.is_empty then ('\255', b0, 0) else
  match compare (i+1) b.length with
    | -1 -> b.contents.[i], b0, i+1
    | 0 -> b.contents.[i], b.next, 0
    | _ -> read b.next (i - b.length)

let rec get (lazy b) i =
  if b.is_empty then '\255' else
  if i < b.length then
    b.contents.[i]
  else
    get b.next (i - b.length)

let gen_ident =
  let c = ref 0 in
  fun () -> let x = !c in c := x + 1; x

let empty_buffer fn lnum bol =
  let rec res =
    lazy { is_empty = true
         ; name     = fn
         ; lnum     = lnum
         ; bol      = bol
         ; length   = 0
         ; contents = ""
         ; next     = res
         ; ident    = gen_ident ()
         }
  in res

let rec is_empty (lazy b) pos =
  if pos < b.length then false
  else if pos = 0 then
    b.is_empty
  else is_empty b.next (pos - b.length)

let fname (lazy b) = b.name

let line_num (lazy b) = b.lnum

let line_beginning (lazy b) = b.bol

let line (lazy b) = b.contents

let rec normalize (lazy b as str) pos =
  if pos >= b.length then
    if b.is_empty then str, 0 else normalize b.next (pos - b.length)
  else str, pos

let lexing_position str pos =
  let bol = line_beginning str in
  Lexing.({ pos_fname = fname str
          ; pos_lnum  = line_num str
          ; pos_cnum  = bol +pos
          ; pos_bol   = bol })

type cont_info = EndOfFile

let buffer_from_fun ?(finalise=(fun _ -> ())) fname get_line data =
  let rec fn fname active num bol cont =
    begin
      let num = num + 1 in
      try
        let line = get_line data in
        let len = String.length line in
        let bol' = bol + len in
        (fun () ->
           if active then (
               { is_empty = false; name = fname; lnum = num; bol; length = len ; contents = line ;
                 next = lazy (fn fname active num bol' cont); ident = gen_ident () })
           else fn fname active num bol' cont)
      with
        End_of_file -> fun () -> finalise data; cont fname EndOfFile num bol
    end ()
  in
  lazy (fn fname true 0 0 (fun fname status line bol ->
  match status with
  | EndOfFile ->
     Lazy.force (empty_buffer fname line bol)))

external unsafe_input : in_channel -> string -> int -> int -> int
                      = "caml_ml_input"

external input_scan_line : in_channel -> int = "caml_ml_input_scan_line"

let input_line chan =
  let rec build_result buf pos = function
    [] -> buf
  | hd :: tl ->
      let len = String.length hd in
      String.blit hd 0 buf (pos - len) len;
      build_result buf (pos - len) tl in
  let rec scan accu len =
    let n = input_scan_line chan in
    if n = 0 then begin                   (* n = 0: we are at EOF *)
      match accu with
        [] -> raise End_of_file
      | _  -> build_result (Bytes.create len) len accu
    end else if n > 0 then begin          (* n > 0: newline found in buffer *)
      let res = Bytes.create n in
      ignore (unsafe_input chan res 0 n);
      match accu with
        [] -> res
      |  _ -> let len = len + n in
              build_result (Bytes.create len) len (res :: accu)
    end else begin                        (* n < 0: newline not found *)
      let beg = Bytes.create (-n) in
      ignore(unsafe_input chan beg 0 (-n));
      scan (beg :: accu) (len - n)
    end
  in scan [] 0

let buffer_from_channel ?(filename="") ch =
  buffer_from_fun filename input_line ch

let buffer_from_file filename =
  let ch = open_in filename in
  buffer_from_fun ~finalise:close_in filename input_line ch

let get_string_line (str, p) =
  let len = String.length str in
  let start = !p in
  if start >= len then raise End_of_file;
  while (!p < len && str.[!p] <> '\n') do
    incr p
  done;
  if !p < len then incr p;
  let len' = !p - start in
  String.sub str start len'

let buffer_from_string ?(filename="") str =
  let data = (str, ref 0) in
  buffer_from_fun filename get_string_line data

type 'a buf_table = (buffer_aux * int * 'a list) list

let empty_buf = []

let eq_buf (lazy b1) (lazy b2) = b1.ident = b2.ident

let cmp_buf (lazy b1) (lazy b2) = b1.ident - b2.ident

let buf_ident (lazy buf) = buf.ident

let leq_buf b1 i1 b2 i2 =
  match (b1, b2) with
    ({ ident=ident1; }, { ident=ident2; }) ->
      (ident1 = ident2 && i1 <= i2) || ident1 < ident2

let insert_buf buf pos x tbl =
  let buf = Lazy.force buf in
  let rec fn acc = function
  | [] -> List.rev_append acc [(buf, pos, [x])]
  | ((buf',pos', y as c) :: rest) as tbl ->
     if pos = pos' && buf.ident = buf'.ident then
       List.rev_append acc ((buf', pos', (x::y)) :: rest)
     else if leq_buf buf pos buf' pos' then
       List.rev_append acc ((buf, pos, [x]) :: tbl)
     else fn (c::acc) rest
  in fn [] tbl

let pop_firsts_buf = function
  | [] -> raise Not_found
  | (buf,pos,l)::rest -> Lazy.from_val buf,pos,l,rest

let iter_buf buf fn =
  List.iter (fun (_,_,l) -> List.iter fn l) buf
