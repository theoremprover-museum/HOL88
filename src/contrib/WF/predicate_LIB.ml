% this file contains TACTICs and RULEs to support theorem proving in
  predicates. It contains:
 
  pseq_TAUT_TAC           : proving predicates tautology

  pseq_TAUT_RULE          : proving predicates tautologu

  pseq_JADE_TAC           : helpful canonical tactic, cannot terminate


%


load_library `taut` ;;
loadf `MYTACTICS` ;;

let pred_defs = snd(split (definitions `predicate`)) ;;


let [EQUAL_DEF; SEQ_DEF] =
   [ (definition `predicate` `==_DEF`) ;
     (definition `predicate` `|==_DEF`) ] ;;


let pseq_TAUT_TAC = 
   REWRITE_TAC pred_defs
   THEN GEN_TAC 
   THEN BETA_TAC
   THEN TAUT_TAC ;;

let pseq_TAUT_RULE trm = prove (trm, pseq_TAUT_TAC) ;;

let pseq_JADE_TAC =
    REWRITE_TAC pred_defs
    THEN BETA_TAC
    THEN (REPEAT STRIP_TAC)
    THEN (REPEAT (ASM_REWRITE_TAC [] THEN RES_TAC)) ;;

let pseq_CYAN_TAC =
    REWRITE_TAC pred_defs THEN BETA_TAC
    THEN REPEAT GEN_TAC THEN EXT_TAC THEN TAUT_TAC ;;


