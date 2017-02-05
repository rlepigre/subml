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

(** Node printing *)
let uNode ch = fprintf ch
"<node id=\"%s\">
 <data key=\"d0\">
  <y:ShapeNode>
   <y:Fill color=\"#88FF88\"/>
   <y:NodeLabel alignment=\"left\">
     %t
   </y:NodeLabel>
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
  </y:PolyLineEdge>
 </data>
</edge>
"

(** Edge printing *)
let revEdge ch = fprintf ch
"<edge source=\"%s\" target=\"%s\">
 <data key=\"d2\">
  <y:PolyLineEdge>
   <y:LineStyle type=\"dotted\" width=\"2\" color=\"#000000\"/>
   <y:Arrows source=\"none\" target=\"delta\"/>
  </y:PolyLineEdge>
 </data>
</edge>
"

let groupBegin ch lbl =
  fprintf ch " <node id=\"%s\" yfiles.foldertype=\"group\">\n" lbl;
  fprintf ch "  <data key=\"d0\">\n";
  fprintf ch "  <y:ProxyAutoBoundsNode>\n";
  fprintf ch "   <y:Realizers active=\"0\">\n";
  fprintf ch "    <y:GroupNode>\n";
  fprintf ch "     <y:Fill color=\"#EEEEFF\"/>\n";
  fprintf ch "    </y:GroupNode>\n";
  fprintf ch "   </y:Realizers>\n";
  fprintf ch "  </y:ProxyAutoBoundsNode>\n";
  fprintf ch " </data>\n";
  fprintf ch " <data key=\"d1\"/>\n";
  fprintf ch " <graph edgedefault=\"directed\" id=\"box\">\n"

let groupEnd ch =
  fprintf ch "</graph>\n";
  fprintf ch "</node>\n"

  (** Proof printing, without header and trailer *)
let to_nodes : formatter -> string proof -> unit = fun ch p ->
  let c = ref 0 in
  let label () = let n = sprintf "N%d" !c in incr c; n in
  let rules = Hashtbl.create 101 in
  let rec to_nodes in_sub = function
    | Hyp(s,n)         ->
       let l = label () in
       node ch l s;
       begin
         match n with
         | None -> ()
         | Some n ->
            let l0 = try Hashtbl.find rules n with Not_found -> assert false in
            revEdge ch l0 l
       end;
       l
    | Rule(ps,c,n,sub) ->
       if sub && not in_sub then groupBegin ch (label ());
       let l0 = label () in
       begin
         match n with None -> ()
                    | Some n -> Hashtbl.add rules n l0
       end;
       let labels = List.map (to_nodes sub) ps in
       node ch l0 c;
       List.iter (fun l -> edge ch l0 l) labels;
       if sub && not in_sub then groupEnd ch;
       l0
  in
  let _ = to_nodes false p in ()

(** Complete proof printing *)
let output : formatter -> Ast.typ_prf -> unit = fun ch p ->
  let open Print in
  let save_mode = !print_mode in
  print_mode := Gml;
  try
    let p = Print.typ2proof p in
    fprintf ch "%s%a%t%s%!"
            head
            to_nodes p
            (fun ch -> uNode ch "index" print_epsilon_tbls)
            tail;
    print_mode := save_mode
  with e ->
    print_mode := save_mode;
    raise e
