(****************************************************************************
 *                     Source code position management                      *
 ****************************************************************************)

type pos =
  { filename   : string (* Name of the file. *)
  ; dummy      : bool   (* Set to true if the position is not real. *)
  ; line_start : int    (* Line number of the starting point. *)
  ; col_start  : int    (* UTF8 column number of the starting point. *)
  ; line_end   : int    (* Line number of the ending point. *)
  ; col_end    : int }  (* UTF8 column number of the ending point. *)

(* Dummy position. *)
let none : pos =
  { filename   = "_none_"
  ; dummy      = true
  ; line_start = 0
  ; col_start  = 0
  ; line_end   = 0
  ; col_end    = 0 }

(* DeCaP location function. *)
let locate buf1 pos1 buf2 pos2 =
  { filename   = Input.fname buf1
  ; dummy      = false
  ; line_start = Input.line_num buf1
  ; col_start  = Input.utf8_col_num buf1 pos1
  ; line_end   = Input.line_num buf2
  ; col_end    = Input.utf8_col_num buf2 pos2 }

type 'a position = { elt : 'a ; pos : pos }

let in_pos : pos -> 'a -> 'a position =
  fun p e -> { elt = e; pos = p }

let dummy_position : pos = none

let dummy_pos : 'a -> 'a position = fun e -> in_pos dummy_position e

type strpos = string position
