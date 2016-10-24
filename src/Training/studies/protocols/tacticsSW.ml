%----------------------------------------------------------------------------%
% TACTICS required for Protocol Case Study                                   %
% Modified for HOL12 on 22/iii/91 by RCO                                     %
%----------------------------------------------------------------------------%

let tactic2 =
  REWRITE_TAC[INIT;DATA_RECV] THEN
  REPEAT GEN_TAC THEN 
  DISCH_TAC THEN
  POP_ASSUM ((MAP_EVERY ASSUME_TAC) o CONJUNCTS) THEN
  IMP_RES_TAC ONE_LESS_0_LESS;;

let tactic3 =
  INDUCT_TAC THENL
  [ ASM_REWRITE_TAC[] ;
    IMP_RES_TAC (SPECL ["(r:^seqtime) t";"1";"maxseq:num"] plusm_less_m) THEN
    UNDISCH_TAC "!t.
        (IN_WINDOW((dataR:^channel) t)(r t)RW maxseq => 
         ((r(t + 1) = plusm(r t,1,maxseq)) /\
          (sink(t + 1) = APPEND(sink t)[message(dataR t)])) | 
         ((r(t + 1) = r t) /\ (sink(t + 1) = sink t)))" THEN
    DISCH_TAC THEN POP_ASSUM(MP_TAC o SPEC "t:^time") THEN
    COND_CASES_TAC THEN 
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADD1] ];;

let tactic5 =
  REWRITE_TAC[CHANNEL] THEN REPEAT STRIP_TAC;;

let tactic6 thm =
  REWRITE_TAC[IN_WINDOW;ACK_TRANS] THEN REPEAT STRIP_TAC THEN 
  UNDISCH_TAC "!t dummy.       (q t => 
         ((ackR:^channel) t = new_packet(subm(r t,1,maxseq))dummy) | 
         (ackR t = set_non_packet))" THEN
  DISCH_TAC THEN POP_ASSUM( MP_TAC o SPEC_ALL) THEN
  COND_CASES_TAC THEN 
    REPEAT STRIP_TAC THEN IMP_RES_TAC thm;;

let tactic7 =
  REWRITE_TAC [DATA_TRANS] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  UNDISCH_TAC "!t. (p t(i t) ==> ~NULL(TLI(i t)(rem t)) /\ (i t) < SW) /\
        ((p t(i t) /\ ~NULL(rem t)) => 
         ((dataS:^channel) t = 
          new_packet(plusm(s t,i t,maxseq))(HDI(i t)(rem t))) | 
         (dataS t = set_non_packet))" THEN
  DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN 
  COND_CASES_TAC THEN 
    DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC;;

let tactic8 =
  ASM_REWRITE_TAC[new_packet;label;message;OUTL;FST;SND] THEN
  POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) THEN
  RES_TAC THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_TAC PRE_LESS_LESS_SUC;;

let tactic10 =
  REWRITE_TAC[IN_WINDOW] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC "(subm(label((dataR:^channel) t),r t,maxseq)) < RW" THEN 
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE[less_than_one_is_0])) THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC;;

let tactic11A lem1 =
  UNDISCH_TAC "IN_WINDOW((dataR:^channel) t)(r t)RW maxseq" THEN
  ASM_REWRITE_TAC[IN_WINDOW] THEN DISCH_TAC THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN 
  IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[];;

let tactic11B lem2 =
  UNDISCH_TAC "good_packet((dataR:^channel) t)" THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL ["dataS:^channel";"maxseq:num";"s:^seqtime";
                 "p:num->^time->bool";"i:^seqtime";
                 "rem:^datatime";"t:^time"] lem2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN  
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "(((i:^seqtime) t) + 1) < maxseq" THEN
  REWRITE_TAC [SYM (SPEC_ALL ADD1)] THEN DISCH_TAC THEN
  IMP_RES_TAC SUC_LESS ;;

let tactic12 lem1 lem2 lem3 =
  REPEAT GEN_TAC THEN DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  IMP_RES_TAC lem3 THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
  UNDISCH_TAC "IN_WINDOW((dataR:^channel) t)(r t)RW maxseq" THEN 
  REWRITE_TAC[IN_WINDOW] THEN DISCH_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  IMP_RES_TAC lem1 THEN
  UNDISCH_TAC "good_packet((dataR:^channel) t)" THEN 
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  IMP_RES_TAC lem2 THEN
  ASM_REWRITE_TAC[];;



let tactic15 thmlist =
  REPEAT GEN_TAC THEN
  REWRITE_TAC thmlist THEN
  STRIP_TAC THEN INDUCT_TAC ;;

let tactic16 thm1 thm2 =
   IMP_RES_TAC thm1 THEN IMP_RES_TAC thm2 THEN
   POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
   IMP_RES_TAC subm_plusm THEN
   POP_ASSUM (ASSUME_TAC o SPECL ["(r:^seqtime) t";"1";"(s:^seqtime) t"]) THEN
   IMP_RES_TAC plusm_eq_plus THEN IMP_RES_TAC HDI_TLI_1 THEN
   ASM_REWRITE_TAC[ADD1;(SYM (SPEC_ALL APPEND_ASSOC));HDI_TLI_2];;


let tactic17 =
 REWRITE_TAC[IMPL] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN 
 POP_ASSUM STRIP_ASSUME_TAC THEN
 ASM_REWRITE_TAC[];;

let tactic18 =
  REWRITE_TAC[DATA_TRANS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[];;

let tactic19 =
  REWRITE_TAC[SENDER;ACK_RECV;ABORT] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC "!t. (IN_WINDOW((ackS:^channel) t)(s t)SW maxseq => 
         ((s(t + 1) = plusm(label(ackS t),1,maxseq)) /\
          ((rem:^datatime)(t + 1) =
           TLI(subm(plusm(label(ackS t),1,maxseq),s t,maxseq))(rem t))) | 
         ((s(t + 1) = s t) /\ (rem(t + 1) = rem t)))" THEN
  DISCH_TAC THEN POP_ASSUM (MP_TAC o SPEC_ALL) THEN
  COND_CASES_TAC THEN REPEAT STRIP_TAC;;

let tactic20 initmax swval =
   EXISTS_TAC "SUC(subm(label((ackS:^channel) t),s t,maxseq))" THEN
   UNDISCH_TAC "IN_WINDOW((ackS:^channel) t)(s t)SW maxseq" THEN
   REWRITE_TAC[IN_WINDOW;LESS_0] THEN REPEAT STRIP_TAC THEN
   IMP_RES_TAC initmax THEN
   let th1 = REWRITE_RULE [SYM SUC_0] (SPECL ["0";"maxseq:num"] LESS_EQ) in
   POP_ASSUM(\th. ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[th1]th)) THEN
   IMP_RES_TAC swval THEN IMP_RES_TAC SUB_ADD THEN
   IMP_RES_TAC subm_plusm THEN
   ASM_REWRITE_TAC[LESS_0;ADD1] THEN
   UNDISCH_TAC  "(subm(label((ackS:^channel) t),s t,maxseq)) < SW" THEN
   ONCE_REWRITE_TAC  [(SYM (SPEC_ALL LESS_MONO_EQ))] THEN
   ASM_REWRITE_TAC [ADD1] THEN  DISCH_TAC THEN
   IMP_RES_TAC plusm_eq_plus THEN
   ASM_REWRITE_TAC[];;

let tactic21 =
  REWRITE_TAC[ABORT] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[];;

let tactic21A =
    GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    POP_ASSUM(DISJ_CASES_TAC o SPEC_ALL);;

let tactic21B =
  POP_ASSUM STRIP_ASSUME_TAC THEN
  UNDISCH_TAC "!t.
      (?x. ((rem:^datatime)(t + 1) = TLI x(rem t)) /\ 0 < x) /\ 
      (c(t + 1) = 0) \/
      (rem(t + 1) = rem t) /\ (c(t + 1) = (c t) + 1)" THEN
  DISCH_TAC THEN  POP_ASSUM(DISJ_CASES_TAC o SPEC "t+n");;

let tactic22 =
  DISJ1_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  EXISTS_TAC "x'+x" THEN
  ASM_REWRITE_TAC[ADD1;HDI_TLI_2] THEN
  IMP_RES_TAC LESS_MONO_ADD THEN
  UNDISCH_TAC "!p. (0 + p) < (x' + p)" THEN DISCH_TAC THEN
  POP_ASSUM(ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES] o SPEC "x:num") THEN
  IMP_RES_TAC LESS_TRANS;;

let tactic23 =
  DISJ1_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
  EXISTS_TAC "x:num" THEN ASM_REWRITE_TAC[ADD1;ADD_CLAUSES];;

let tactic28 =
  IMP_RES_TAC NULL_LENGTH_0 THEN
  POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES;LESS_OR_EQ_0] ;;

let tactic29 =
  POP_ASSUM STRIP_ASSUME_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[HDI_TLI_3] THEN
  IMP_RES_TAC useful_lemma ;;

let tactic30 live liveassum lemma =
  REPEAT STRIP_TAC THEN IMP_RES_TAC live THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC (SPECL ["aborted:^time->bool";"maxT:^time"] liveassum) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[IMP_DISJ_THM]) THEN
  IMP_RES_TAC lemma THEN
  POP_ASSUM (ASSUME_TAC o SPEC "LENGTH ((rem:^datatime) 0)") ;;

