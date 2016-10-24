% ld_proof1.ml

  load the theory of proofs
%

load_library `finite_sets`;;
load_library `more_lists`;;
extend_theory `proof`;;
load_library `string`;;
load_library `taut`;;
loadt `defs/ld_pair`;;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;

autoload_defs `proofaux`;;
autoload_thms `proofaux`;;
autoload_defs `Type`;;
autoload_thms `Type`;;
autoload_defs `Pterm`;;
autoload_thms `Pterm`;;
autoload_defs `inference`;;
autoload_thms `inference`;;
autoload_defs `proof`;;
autoload_thms `proof`;;

loadf `defs/defs`;;
loadf `Type/Type_convs`;;
loadf `Proof/proof_convs`;;

loadf `Rules/mk_proof_pretty`;;
loadf `Rules/mk_proof_rules1`;;
loadf `Rules/mk_proof_rules2`;;

