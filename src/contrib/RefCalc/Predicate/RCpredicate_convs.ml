% File: RCpredicate_convs.ml
   
  some infrastructure for doing proofs about predicates
%


% --- simple prover for tautologous formulas --- %

let PRED_TAUT_TAC =
 let rwlist = [false_DEF;true_DEF;not_DEF;and_DEF;or_DEF;
               imp_DEF;implies_DEF]
 and FUN_TAC = CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC
 in REPEAT GEN_TAC THEN REWRITE_TAC rwlist THEN BETA_TAC THEN
    (FUN_TAC ORELSE GEN_TAC ORELSE ALL_TAC) THEN TAUT_TAC;;
