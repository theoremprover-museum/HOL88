% File: mk_RCrecursion2.ml
   strictness of recursion
%



let thm1 = prove("~t==>~t' = t'==>t",TAUT_TAC);;
let thm2 = prove("(q:^pred) implies true",PRED_TAUT_TAC);;
let thm3 = prove
 ("(!c. strict c ==> strict((f:^ptrans12->^ptrans12) c))
    ==> (mu f) ref (\q. ((q = false) => false | true))",
  DISCH_THEN(MP_TAC o SPEC "\q:^pred1.(q=false)=>false:^pred2|true") THEN
  PORT[strict_DEF] THEN BETA_TAC THEN RT[] THEN DISCH_TAC THEN
  MATCH_MP_TAC mu_least THEN CONJ_TAC THENL
  [LRT[monotonic_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
   DISCH_TAC THEN GEN_TAC THEN ASM_CASES_TAC "p:^pred1=false" THEN ART[] THENL
   [RT[false_DEF] THEN BETA_TAC THEN RT[]
   ;ASM_CASES_TAC "q:^pred1=false" THEN ART[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN LRT[true_DEF;false_DEF] THEN
    PORT[thm1] THEN DISCH_THEN(\t. POP_ASSUM MP_TAC THEN RT[t]) THEN
    DISCH_TAC THEN FUN_TAC THEN ART[]
   ]
  ;LRT[ref_DEF;implies_DEF] THEN BETA_TAC THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC "q:^pred1=false" THEN ART[true_DEF] THEN BETA_TAC THEN RT[]
  ]);;
let thm4 = prove
 ("!c:^ptrans12. c ref (\q. ((q = false) => false | true)) ==> strict c",
  GEN_TAC THEN LRT[ref_DEF;strict_DEF;ref_DEF;implies_DEF;false_DEF] THEN
  BETA_TAC THEN DISCH_THEN (MP_TAC o SPEC"\v:*s1.F") THEN RT[] THEN
  DISCH_TAC THEN FUN_TAC THEN ART[]);;
let strict_mu = IMP_TRANS thm3 (ISPEC"mu(f:^ptrans12->^ptrans12)"thm4);;
% strict_mu = |- (!c. strict c ==> strict(f c)) ==> strict(mu f) %


save_thm(`strict_mu`,strict_mu);;

