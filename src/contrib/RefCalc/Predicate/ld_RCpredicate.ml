% File: ld_RCpredicate.ml
   Loads the RCpredicate theory
%

extend_theory `RCpredicate`;;

let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and pred3 = ":^state3->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans13 = ":^pred1->^pred3"
 and ptrans23 = ":^pred2->^pred3"
 and ptrans31 = ":^pred3->^pred1";;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;

loadf `defs`;;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;

autoload_defs `RCpredicate`;;
autoload_thms `RCpredicate`;;
loadf `Predicate/RCpredicate_convs`;;
