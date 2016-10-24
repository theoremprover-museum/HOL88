% File: mk_RCwintool.ml
   Builds the RCwintool theory 
%

new_theory `RCwintool`;;
new_parent `RCdataref`;;

load_library `window`;;


let  state  = ":*s"
 and estate = ":*#*s"
 and astate = ":*a#*s"
 and cstate = ":*c#*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3";;
let arel = ":(*a#*c#*s)->bool";;
let  pred  = ":^state->bool"
 and epred = ":^estate->bool"
 and apred = ":^astate->bool"
 and cpred = ":^cstate->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool"
 and pred3 = ":^state3->bool";;
let  ptrans  = ":^pred->^pred"
 and eptrans = ":^epred->^epred"
 and ptrans11 = ":^pred1->^pred1"
 and ptrans12 = ":^pred1->^pred2"
 and ptrans13 = ":^pred1->^pred3"
 and ptrans23 = ":^pred2->^pred3"
 and aptrans = ":^apred->^apred"
 and cptrans = ":^cpred->^cpred"
 and acptrans = ":^apred->^cpred";;

loadf `defs`;;

loadf `Wintool/mk_RCwintool1`;;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;

load_library `pair`;;

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

autoload_defs `RCcorrect`;;
autoload_thms `RCcorrect`;;
loadf `Correct/RCcorrect_convs`;;

autoload_defs `RCrefine`;;
autoload_thms `RCrefine`;;

autoload_defs `RCrecursion`;;
autoload_thms `RCrecursion`;;

autoload_defs `RCdataref`;;
autoload_thms `RCdataref`;;
loadf `Dataref/RCdataref_convs`;;

loadf `Wintool/mk_RCwintool2`;;
loadf `Wintool/mk_RCwintool3`;;

close_theory();;
