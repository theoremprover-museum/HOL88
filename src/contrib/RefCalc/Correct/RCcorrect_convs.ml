% File: RCcorrect_convs.ml

  conversions and tactics for total correctness proofs
%

let assign_correct_TAC thl =
   LRT[correct_DEF;assign_DEF;implies_DEF;PAIR_EQ] THEN PBETA_TAC THEN
   ((REPEAT STRIP_TAC THEN ART thl THEN FAIL_TAC ``) ORELSE ALL_TAC);;
let nondass_correct_TAC thl =
   LRT[correct_DEF;nondass_DEF;implies_DEF;PAIR_EQ] THEN PBETA_TAC THEN
   ((REPEAT STRIP_TAC THEN ART thl THEN FAIL_TAC ``) ORELSE ALL_TAC);;
let seq_correct_TAC med =
   MATCH_MP_TAC correct_seq THEN EXISTS_TAC med THEN PBETA_TAC THEN
   REPEAT CONJ_TAC THENL [mono_TAC;ALL_TAC;ALL_TAC];;
let cond_correct_TAC =
   MATCH_MP_TAC correct_cond THEN CONJ_TAC;;
let do_correct_TAC inv bound thl =
   MATCH_MP_TAC correct_do THEN EXISTS_TAC inv THEN EXISTS_TAC bound THEN
   REPEAT CONJ_TAC THENL
   [mono_TAC
   ;PORT[implies_DEF] THEN PBETA_TAC THEN REPEAT STRIP_TAC THEN
    ART thl THEN RES_TAC
   ;LPORT[implies_DEF;and_DEF;not_DEF] THEN PBETA_TAC THEN
    LPORT[DE_MORGAN_THM;NOT_CLAUSES] THEN REPEAT STRIP_TAC THEN ART thl
   ;ALL_TAC
   ];;

let STATE_GEN_TAC state = P_PGEN_TAC state THEN PBETA_TAC THEN RT[];;
let CASE_TAC t thm thl =
   MP_TAC (ISPEC t thm) THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN
   LRT thl THEN RT[];;
let BOUND_TAC = STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN ART[];;
