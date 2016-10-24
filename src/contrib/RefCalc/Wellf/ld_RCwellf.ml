% File: ld_RCwellf.ml
   Loads the RCwellf theory
%

extend_theory `RCwellf`;;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;

loadf `defs`;;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;

autoload_defs `RCwellf`;;
autoload_thms `RCwellf`;;
