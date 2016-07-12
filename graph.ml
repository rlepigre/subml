open Proof
open Format

let head = "<!DOCTYPE html>
<html>
  <head>
  <meta charset=\"utf-8\">
  <meta http-equiv=\"X-UA-Compatible\" content=\"IE=edge,chrome=1\">
  <meta name=\"viewport\" content=\"width=device-width\">
  <title> Collapsable example </title>
  <link rel=\"stylesheet\" href=\"Treant.css\">
  <link rel=\"stylesheet\" href=\"collapsable.css\">
</head>
<body>
  <div class=\"chart\" id=\"proof\"></div>
  <script src=\"vendor/raphael.js\"></script>
  <script src=\"Treant.js\"></script>
  <script src=\"vendor/jquery.min.js\"></script>
  <script src=\"vendor/jquery.easing.js\"></script>
  <script>
    var nodes = "

let tail = ";

    tree = new Treant(
      { chart:
        { container     : \"#proof\"
        , animateOnInit : true
        , node          : { collapsable: true }
        , animation     :
          { nodeAnimation: \"easeOutBounce\"
          , nodeSpeed    : 700
          , connectorsAnimation: \"bounce\",
                connectorsSpeed: 700
            }
        }
        , nodeStructure: nodes});
  </script>
</body>
</html>"

let to_nodes : formatter -> string proof -> unit = fun ch p ->
  let rec to_nodes ch = function
    | Hyp(s)       -> fprintf ch "{ innerHTML: \"%s\" }" s
    | Rule(ps,c,_) -> fprintf ch "{ innerHTML: \"%s\", collapsed: false," c;
                      let rec children ch = function
                        | []  -> ()
                        | [c] -> to_nodes ch c
                        | cs  -> List.iter (fprintf ch "%a, " to_nodes) cs
                      in
                      fprintf ch "children: [%a]}" children ps
  in to_nodes ch p

let output_html : formatter -> string proof -> unit = fun ch p ->
  fprintf ch "%s%a%s%!" head to_nodes p tail
