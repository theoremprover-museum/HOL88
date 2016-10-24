% File: mk_RCdataref.ml %

% make the theory RCdataref %


new_theory `RCdataref`;;
new_parent `RCrecursion`;;

let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and astate = ":*a#*s"
 and cstate = ":*c#*s";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and apred = ":^astate->bool"
 and cpred = ":^cstate->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans22 = ":^pred2->^pred2"
 and aptrans = ":^apred->^apred"
 and cptrans = ":^cpred->^cpred"
 and acptrans = ":^apred->^cpred"
 and captrans = ":^cpred->^apred";;
let arel = ":*a#*c#*s->bool";;

loadf `Dataref/mk_RCdataref1`;;

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

loadf `Dataref/mk_RCdataref2`;;

close_theory();;
