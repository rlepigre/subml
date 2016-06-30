(* boolean, Church encoding, typed *)
typed;

type Bool = ∀X (X → X → X);

let True = (fun x y ↦ x) : Bool;
let False = (fun x y ↦ y) : Bool;

let if = λb:Bool x y.b x y;
let or  : (Bool → Bool → Bool)b1 b2 = b1 True b2;
let an  : (Bool → Bool → Bool) b1 b2 = b1 b2 False;
let not : (Bool → Bool) b1 = b1 False True;