(****************************************************************************
 *                     Source code position management                      *
 ****************************************************************************)

open Lexing

type pos =
  { loc_start : position
  ; loc_end   : position
  ; loc_ghost : bool }

let in_file pos_fname =
  let loc = { pos_fname ; pos_lnum = 1 ; pos_bol = 0 ; pos_cnum = -1 } in
  { loc_start = loc ; loc_end = loc ; loc_ghost = true }

let none = in_file "_none_"

let locate str1 pos1 str2 pos2 =
  let loc_start = Input.lexing_position str1 pos1 in
  let loc_end   = Input.lexing_position str2 pos2 in
  { loc_start ; loc_end ; loc_ghost = false }

type 'a position = { elt : 'a ; pos : pos }

let in_pos : pos -> 'a -> 'a position =
  fun p e -> { elt = e; pos = p }

let dummy_position : pos = none

let dummy_pos : 'a -> 'a position = fun e -> in_pos dummy_position e

type strpos = string position
