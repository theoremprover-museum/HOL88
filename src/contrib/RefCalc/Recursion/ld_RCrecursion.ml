% File: ld_RCrecursion.ml
   Loads the RCrecursion theory
%

extend_theory `RCrecursion`;;

let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3"
 and state4 = ":*s4"
 and state5 = ":*s5"
 and estate = ":*#*s";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and pred3 = ":^state3->bool"
 and pred4 = ":^state4->bool"
 and pred5 = ":^state5->bool"
 and epred = ":^estate->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans13 = ":^pred1->^pred3"
 and ptrans23 = ":^pred2->^pred3"
 and ptrans31 = ":^pred3->^pred1"
 and ptrans34 = ":^pred3->^pred4"
 and ptrans45 = ":^pred4->^pred5"
 and eptrans = ":^epred->^epred";;

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

autoload_defs `RCcommand`;;
autoload_thms `RCcommand`;;
loadf `Command/RCcommand_convs`;;

autoload_defs `RCwellf`;;
autoload_thms `RCwellf`;;

autoload_defs `RCcorrect`;;
autoload_thms `RCcorrect`;;
load_library `pair`;;
loadf `Correct/RCcorrect_convs`;;

autoload_defs `RCrefine`;;
autoload_thms `RCrefine`;;

autoload_defs `RCrecursion`;;
autoload_thms `RCrecursion`;;
loadf `Recursion/RCrecursion_convs`;;
