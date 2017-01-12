(** Source code position management. This module can be used to map the
    elements of an abstract syntax tree to sequences of characters in a
    source file. *)


(** Type of a position corresponding to a continuous range of characters in
    a (utf8 encoded) source file. *)
type pos =
  { fname      : string (** File name associated to the position.       *)
  ; start_line : int    (** Line number of the starting point.          *)
  ; start_col  : int    (** Column number (utf8) of the starting point. *)
  ; end_line   : int    (** Line number of the ending point.            *)
  ; end_col    : int    (** Column number (utf8) of the ending point.   *)
  }

(** Convenient short name for an optional position. *)
type popt = pos option

(** Type constructor extending a type (e.g. an element of an abstract syntax
    tree) with a source code position. *)
type 'a loc =
  { elt : 'a   (** The element that is being localised.        *)
  ; pos : popt (** Position of the element in the source code. *)
  }

(** Localised string type (widely used). *)
type strloc = string loc

(** [build_pos pos elt] associates the position [pos] to [elt]. *)
let build_pos : popt -> 'a -> 'a loc =
  fun pos elt -> { elt ; pos }

(** [in_pos pos elt] associates the position [pos] to [elt]. *)
let in_pos : pos -> 'a -> 'a loc =
  fun p elt -> { elt ; pos = Some p }

(** [none elt] wraps [elt] in a localisation structure with no specified
    source position. *)
let none : 'a -> 'a loc =
  fun elt -> { elt ; pos = None }

let merge : pos -> pos -> pos = fun p1 p2 ->
  match compare p1.start_line p2.start_line with
  | n when n < 0 -> {p1 with end_line = p2.end_line ; end_col = p2.end_col}
  | n when n > 0 -> {p2 with end_line = p1.end_line ; end_col = p1.end_col}
  | _ (* n=0 *)  -> let start_col = min p1.start_col p2.start_col in
                    let end_col   = max p1.start_col p2.start_col in
                    {p1 with start_col ; end_col}

let union : popt -> popt -> popt = fun p1 p2 ->
  match (p1, p2) with
  | (None   , None   ) -> None
  | (Some _ , None   ) -> p1
  | (None   , Some _ ) -> p2
  | (Some p1, Some p2) -> Some (merge p1 p2)

(** [locate buf1 pos1 buf2 pos2] builds a position structure given two
    DeCaP input buffers. This function can be used by DeCaP to generate
    the position of elements during parsing.
    @see <http://lama.univ-savoie.fr/decap/> DeCap *)
let locate buf1 pos1 buf2 pos2 =
  { fname      = Input.filename buf1
  ; start_line = Input.line_num buf1
  ; start_col  = (Input.utf8_col_num buf1 pos1) + 1
  ; end_line   = Input.line_num buf2
  ; end_col    = Input.utf8_col_num buf2 pos2
  }

(** [pos_to_string pos] transforms the position [pos] into a readable
    format. *)
let pos_to_string : pos -> string =
  fun p ->
    if p.start_line <> p.end_line then
      Printf.sprintf "file <%s>, position %d:%d to %d:%d"
        p.fname p.start_line p.start_col p.end_line p.end_col
    else if p.start_col = p.end_col then
      Printf.sprintf "file <%s>, line %d, character %d"
        p.fname p.start_line p.start_col
    else
      Printf.sprintf "file <%s>, line %d, characters %d to %d"
        p.fname p.start_line p.start_col p.end_col

(** [print_pos oc pos] prints the position [pos] to the channel [oc]. *)
let print_pos : out_channel -> pos -> unit =
  fun ch p -> output_string ch (pos_to_string p)

(** [short_pos_to_string pos] is similar to [pos_to_string pos] but uses
    a shorter format. *)
let short_pos_to_string : pos -> string =
  fun p ->
    Printf.sprintf "%s, %d:%d-%d:%d"
      p.fname p.start_line p.start_col p.end_line p.end_col

(** [print_short_pos oc pos] prints the position [pos] to the channel [oc]
    using a shorter format that [print_pos oc pos]. *)
let print_short_pos : out_channel -> pos -> unit =
  fun ch p -> output_string ch (short_pos_to_string p)
