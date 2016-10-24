% File: mk_RCrecursion.ml
   Builds the RCrecursion theory
%

new_theory `RCrecursion`;;
new_parent `RCrefine`;;


let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3"
 and state4 = ":*s4"
 and state5 = ":*s5";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and pred3 = ":^state3->bool"
 and pred4 = ":^state4->bool"
 and pred5 = ":^state5->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans13 = ":^pred1->^pred3"
 and ptrans23 = ":^pred2->^pred3"
 and ptrans31 = ":^pred3->^pred1"
 and ptrans34 = ":^pred3->^pred4"
 and ptrans45 = ":^pred4->^pred5";;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;

let autoload_defs thy =
  map (\name. autoload_theory(`definition`,thy,name))
      (map fst (definitions thy));;
let autoload_thms thy =
  map (\name. autoload_theory(`theorem`,thy,name))
      (map fst (theorems thy));;
autoload_defs `RCpredicate`;;
autoload_thms `RCpredicate`;;
loadf `Predicate/RCpredicate_convs`;;

autoload_defs `RCcommand`;;
autoload_thms `RCcommand`;;
loadf `Command/RCcommand_convs`;;

autoload_defs `RCwellf`;;
autoload_thms `RCwellf`;;

autoload_defs `RCcorrect`;;
autoload_thms `RCcorrect`;;

autoload_defs `RCrefine`;;
autoload_thms `RCrefine`;;

loadf `defs`;;

loadf `Recursion/mk_RCrecursion1`;;
loadf `Recursion/mk_RCrecursion2`;;

close_theory();;
