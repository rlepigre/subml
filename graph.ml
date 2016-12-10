(*****************************************************************************)
(**{3                       GraphML proof printing                          }*)
(*****************************************************************************)
open Proof
open Format

(** The goal of this module is to render proof as graphml
    that are easy to navigate with Yed *)

(** File header *)
let head = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns/graphml\"
  xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"
  xmlns:y=\"http://www.yworks.com/xml/graphml\"
  xsi:schemaLocation=\"http://graphml.graphdrawing.org/xmlns/graphml
                      http://www.yworks.com/xml/schema/graphml/1.0/ygraphml.xsd\">
<key for=\"node\" id=\"d0\" yfiles.type=\"nodegraphics\"/>
<key attr.name=\"url\" attr.type=\"string\" for=\"node\" id=\"d0\"/>
<key for=\"edge\" id=\"d2\" yfiles.type=\"edgegraphics\"/>
<key attr.name=\"description\" attr.type=\"string\" for=\"node\" id=\"d2\"/>
<graph edgedefault=\"directed\" id=\"Typing map\">
"

(** File trailer *)
let tail = "</graph>
</graphml>
"
(** Node printing *)
let node ch = fprintf ch
"<node id=\"%s\">
 <data key=\"d0\">
  <y:ShapeNode>
   <y:Fill color=\"#88FF88\"/>
   <y:NodeLabel>%s</y:NodeLabel>
   <y:Shape type=\"rectangle\"/>
  </y:ShapeNode>
 </data>
</node>
"

(** Edge printing *)
let edge ch = fprintf ch
"<edge source=\"%s\" target=\"%s\">
 <data key=\"d2\">
  <y:PolyLineEdge>
   <y:LineStyle type=\"line\" width=\"2\" color=\"#000000\"/>
   <y:Arrows source=\"delta\" target=\"none\"/>
   <y:EdgeLabel visible=\"false\">Less</y:EdgeLabel>
  </y:PolyLineEdge>
 </data>
</edge>
"

(** Proof printing, without header and trailer *)
let to_nodes : formatter -> string proof -> unit = fun ch p ->
  let c = ref 0 in
  let label () = let n = sprintf "node::[%d]" !c in incr c; n in
  let rec to_nodes = function
    | Hyp(s)       -> let l = label () in node ch l s; l
    | Rule(ps,c,_) -> let labels = List.map to_nodes ps in
                      let l0 = label () in node ch l0 c;
                      List.iter (fun l -> edge ch l0 l) labels;
                      l0
  in
  let _ = to_nodes p in ()

(** Complete proof printing *)
let output_graphml : formatter -> string proof -> unit = fun ch p ->
  fprintf ch "%s%a%s%!" head to_nodes p tail
