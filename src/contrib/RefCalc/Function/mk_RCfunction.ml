% File: mk_RCfunction.ml
   functional abstraction
%


new_theory `RCfunction`;;
new_parent `RCrefine`;;


let  state  = ":*s"
 and state1 = ":*s1"
 and state2 = ":*s2"
 and state3 = ":*s3";;
let  pred  = ":^state->bool"
 and pred1 = ":^state1->bool"
 and pred2 = ":^state2->bool";;
let  ptrans  = ":^pred->^pred"
 and ptrans12 = ":^pred1->^pred2";;

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

autoload_defs `RCwellf`;;
autoload_thms `RCwellf`;;

autoload_defs `RCcorrect`;;
autoload_thms `RCcorrect`;;

autoload_defs `RCrefine`;;
autoload_thms `RCrefine`;;

loadf `defs`;;


% --- The function fcall abstraction --- %

let fcall_DEF = new_definition(`fcall_DEF`,
  "fcall c = \u:*s2. @v:*s1. glb(\q. c q u)v");;

% --- the fcall operator is function fcall --- %

let assign_fcall = 
 let thm1 = prove
  ("(\v. !p. p((e:*s2->*s1)x) ==> p v)(e x)",
   BETA_TAC THEN REPEAT STRIP_TAC THEN ART[]) in
 let thm2 = prove
 ("(\v. !p. p((e:*s2->*s1)x) ==> p v)y ==> (y = e x)",
   BETA_TAC THEN DISCH_THEN 
     (ACCEPT_TAC o RR[] o BETA_RULE o SPEC "\z.z=(e:*s2->*s1)x") THEN
   REPEAT STRIP_TAC THEN ART[]) in
 prove("fcall (assign (e:*s2->*s1)) = e",
  LPORT[fcall_DEF;glb_DEF;assign_DEF] THEN FUN_TAC THEN
  ACCEPT_TAC (MATCH_MP thm2 (SELECT_INTRO thm1)));;
let nondass_ref = prove
 ("nondass(P:*s1->*s2->bool) ref (nondass Q) = !u v. Q u v ==> P u v",
  LPORT[ref_DEF;nondass_DEF;implies_DEF] THEN BETA_TAC THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o RR[] o BETA_RULE o
    SPECL["\v'.(P:*s1->*s2->bool)u v'";"u:*s1"]) THEN
  POP_ASSUM MATCH_ACCEPT_TAC);;
let assign_nondass = prove
 ("assign e:^ptrans12 = nondass (\v v'. v' = e v)",
  FUN_TAC THEN LPORT[assign_DEF;nondass_DEF] THEN FUN_TAC THEN
  CONV_TAC (DEPTH_CONV FORALL_1PT_CONV) THEN REFL_TAC);;
let lemma1 = prove
 ("uniconjunctive (c:^ptrans12)
   ==> (assign e) ref c /\ strict c ==> c ref (assign e)",
  DISCH_TAC THEN IMP_RES_TAC nondass_complete THEN POART[] THEN
  LPORT[assign_nondass;nondass_ref;strict_nondass;implies_DEF] THEN
  BETA_TAC THEN CONV_TAC (DEPTH_CONV FORALL_1PT_CONV) THEN
  REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o SPEC "u:*s2") THEN STRIP_TAC THEN
  RES_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN POP_ASSUM ACCEPT_TAC);;
let lemma2 = prove
 ("(assign e) ref (c:^ptrans12) ==> terminating c",
  LPORT[ref_DEF;assign_DEF;terminating_DEF;implies_DEF;true_DEF] THEN
  BETA_TAC THEN DISCH_THEN(ASSUME_TAC o RR[] o BETA_RULE
    o SPEC "\v:*s1.T") THEN FUN_TAC THEN ART[]);;
let lemma3 = prove
 ("!c:^ptrans12. !e. conjunctive c /\ strict c /\ (assign e) ref c
   ==> (c = assign e)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (C1(C2 ref_prop)) THEN ART[] THEN
  IMP_RES_TAC lemma2 THEN IMP_RES_TAC (PORR[uniconj_conjterm] lemma1));;
let fcall_thm = prove
 ("!c:^ptrans12. !f. conjunctive c /\ strict c /\
    (!u0. correct(\u.u = u0)c(\v.v = f u0))
     ==> (fcall c = f)",
  REPEAT STRIP_TAC THEN IMP_RES_TAC conj_mono THEN
  IMP_RES_TAC impl_assign THEN IMP_RES_TAC lemma3 THEN
  ART[assign_fcall]);;

let fcall_rule = prove
 ("!c:^ptrans12. !f. conjunctive c /\ strict c /\ (assign f) ref c
   ==> (fcall c = f)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC fcall_thm THEN ART[] THEN GEN_TAC THEN
  POP_ASSUM MP_TAC THEN LPORT[ref_DEF;correct_DEF;assign_DEF;implies_DEF] THEN
  BETA_TAC THEN STRIP_TAC THEN CONV_TAC FORALL_1PT_CONV THEN
  POP_ASSUM MATCH_MP_TAC THEN BETA_TAC THEN REFL_TAC);;


% --- fcall under precondition --- %

let thm1 = prove
 ("(!u0. P u0 ==> correct(\u. u = u0)(c:^ptrans12)(\v. v = f u0))
   ==> correct(\u. u = u0)(cond P c (assign f))(\v. v = f u0)",
  LPORT[correct_DEF;cond_DEF;assign_DEF;and_DEF;or_DEF;not_DEF;implies_DEF]
  THEN BETA_TAC THEN CONV_TAC (DEPTH_CONV FORALL_1PT_CONV) THEN
  ASM_CASES_TAC "(P:*s2->bool)u0" THEN ART[] THEN REPEAT STRIP_TAC THEN
  RES_TAC);;
let fcall_thm_pre = prove
 ("!g. !c:^ptrans12. !f. conjunctive c /\ strict c /\
    (!u0. g u0 ==> correct (\u.u = u0) c (\v.v = f u0))
    ==> (!u. g u ==> (fcall c u = f u))",
  REPEAT STRIP_TAC THEN IMP_RES_TAC thm1 THEN 
  ASSUM_LIST (\l. ASSUME_TAC(MATCH_MP conj_cond
     (CONJ(el 5 l)(ISPEC "f:*s2->*s1" conj_assign)))) THEN
  ASSUM_LIST (\l. ASSUME_TAC(MATCH_MP strict_cond
     (CONJ(el 5 l)(ISPEC "f:*s2->*s1" strict_assign)))) THEN
  ASSUM_LIST (\l. ASSUME_TAC(MATCH_MP fcall_thm
     (CONJ(ISPEC "g:*s2->bool"(el 2 l))
          (CONJ(ISPEC "g:*s2->bool"(hd l))(el 3 l))))) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN PORT[fcall_DEF] THEN BETA_TAC THEN
  LPORT[cond_DEF;assign_DEF;or_DEF;and_DEF;not_DEF] THEN BETA_TAC THEN
  ART[]);;

let lemma = prove
 ("!g e. ((assert g) seq (assign e)) ref(c:^ptrans12)
    ==> (!u0. g u0 ==> correct(\u. u = u0)c(\v. v = e u0))",
  LPORT[ref_DEF;seq_DEF;assert_DEF;assign_DEF;correct_DEF] THEN
  LPORT[implies_DEF;and_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  BETA_TAC THEN ART[]);;
let fcall_rule_pre = prove
 ("!g. !c:^ptrans12. !f. conjunctive c /\ strict c /\
       ((assert g) seq (assign f)) ref c
       ==> (!u. g u ==> (fcall c u = f u))",
  REPEAT STRIP_TAC THEN
  ASSUM_LIST(\l. ASSUME_TAC(MATCH_MP lemma (el 2 l))) THEN
  IMP_RES_TAC fcall_thm_pre);;


save_thm(`assign_fcall`,assign_fcall);;
save_thm(`fcall_thm`,fcall_thm);;
save_thm(`fcall_rule`,fcall_rule);;
save_thm(`fcall_thm_pre`,fcall_thm_pre);;
save_thm(`fcall_rule_pre`,fcall_rule_pre);;

close_theory();;
