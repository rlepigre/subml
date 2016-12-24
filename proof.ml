(****************************************************************************)
(**{3             Helper function to print and build prooftree             }*)
(****************************************************************************)
open Format

type 'a proof =
  (* Hypothesis. *)
  | Hyp  of 'a
  (* Rule: premises, conclusion, name. *)
  | Rule of 'a proof list * 'a * 'a option

(* Map function on proofs. *)
let rec map : ('a -> 'b) -> 'a proof -> 'b proof = fun f p ->
  match p with
  | Hyp(h)               -> Hyp(f h)
  | Rule(ps, c, None   ) -> Rule(List.map (map f) ps, f c, None     )
  | Rule(ps, c, Some(n)) -> Rule(List.map (map f) ps, f c, Some(f n))

(* Smart constructor for proofs. *)
let hyp h = Hyp(h)

let n_ary c ps         = Rule(ps, c, None)
let axiom c            = n_ary c []
let unary c p          = n_ary c [p]
let binary c p1 p2     = n_ary c [p1;p2]
let ternary c p1 p2 p3 = n_ary c [p1;p2;p3]

let n_aryN n c ps         = Rule(ps, c, Some(n))
let axiomN n c            = n_aryN n c []
let unaryN n c p          = n_aryN n c [p]
let binaryN n c p1 p2     = n_aryN n c [p1;p2]
let ternaryN n c p1 p2 p3 = n_aryN n c [p1;p2;p3]

(* Proof printing functions. *)
let output : formatter -> string proof -> unit = fun ch p ->
  let output_name ch = function
    | None    -> ()
    | Some(n) -> fprintf ch "  \\RightLabel{$%s$}\n" n
  in
  let macro_name = function
    | 1 -> "Unary"
    | 2 -> "Binary"
    | 3 -> "Trinary"
    | 4 -> "Quaternary"
    | 5 -> "Quinary"
    | _ -> assert false
  in
  let rec output ch = function
    | Hyp(s)         -> fprintf ch "  \\AxiomC{$%s$}\n" s
    | Rule(ps, c, n) -> List.iter (output ch) ps;
                        if ps = [] then fprintf ch "  \\AxiomC{}\n";
                        output_name ch n;
                        let macro = macro_name (max 1 (List.length ps)) in
                        fprintf ch "  \\%sInfC{$%s$}\n" macro c;
  in
  fprintf ch "\\begin{prooftree}\n%a\\end{prooftree}\n%!" output p
