% File: mk_RCpredicate.ml
   Builds the RC theories
%

let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool";;
let ptrans = ":^pred->^pred";;

new_theory `RCpredicate`;;

loadf `Predicate/mk_RCpredicate1`;;

load_library `taut`;;
let TAUT t = TAC_PROOF(([],t),TAUT_TAC);;
loadf `defs`;;
let PRED_TAUT_TAC =
 let rwlist = [false_DEF;true_DEF;not_DEF;and_DEF;or_DEF;
               imp_DEF;implies_DEF]
 and FUN_TAC = CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC
 in REPEAT GEN_TAC THEN RT rwlist THEN BETA_TAC THEN
    (FUN_TAC ORELSE GEN_TAC ORELSE ALL_TAC) THEN TAUT_TAC;;

loadf `Predicate/mk_RCpredicate2`;;

close_theory();;
