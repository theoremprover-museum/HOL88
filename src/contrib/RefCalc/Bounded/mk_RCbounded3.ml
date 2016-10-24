% File: mk_RCbounded3.ml
  continuity of commands
%



% --- continuity of program constructs --- %

% --- abort --- %
let ucont_abort = prove
 ("ucontinuous (abort:^ptrans12)",
  LPORT[ucontinuous_DEF;abort_DEF;ulimit_DEF;false_DEF] THEN BETA_TAC THEN
  REPEAT STRIP_TAC THEN FUN_TAC THEN RT[]);;

% --- skip --- %
let ucont_skip = TAC_PROOF
 (([],"ucontinuous (skip:^ptrans)"),
  LPORT[ucontinuous_DEF;skip_DEF;ulimit_DEF] THEN BETA_TAC THEN RT[]);;

% --- assign --- %
let ucont_assign = TAC_PROOF
 (([],"ucontinuous (assign (e:^state1->^state2))"),
  LPORT[ucontinuous_DEF;assign_DEF;ulimit_DEF] THEN BETA_TAC
  THEN REPEAT STRIP_TAC THEN REFL_TAC);;

% --- assert --- %
let ucont_assert = TAC_PROOF
 (([],"ucontinuous (assert (b:^pred))"),
  LPORT[ucontinuous_DEF;assert_DEF;and_DEF;ulimit_DEF]
  THEN REPEAT STRIP_TAC THEN FUN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
  [EXISTS_TAC "n:num" THEN ART[]
  ;FIRST_ASSUM ACCEPT_TAC
  ;EXISTS_TAC "n:num" THEN FIRST_ASSUM ACCEPT_TAC
  ]);;

% --- guard --- %
let ucont_guard = prove
 ("ucontinuous (guard (b:^pred))",
  LPORT[ucontinuous_DEF;guard_DEF;imp_DEF;ulimit_DEF]
  THEN REPEAT STRIP_TAC THEN FUN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
  [ASM_CASES_TAC "(b:^pred)x" THEN RES_TAC THEN ART[] THEN
   EXISTS_TAC "n:num" THEN ART[]
  ;EXISTS_TAC "n:num" THEN RES_TAC
  ]);;

% --- dch --- %
let ucont_dch = prove
 ("ucontinuous (c:^ptrans12) /\ ucontinuous c' ==> ucontinuous (c dch c')",
  LPORT[ucontinuous_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  PORT[dch_DEF] THEN ART[] THEN LPORT[and_DEF;ulimit_DEF] THEN FUN_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL
  [EXISTS_TAC "n+n'" THEN IMP_RES_TAC 
   (LPORR[ucontinuous_DEF;monotonic_DEF;implies_DEF] ucont_mono)
   THEN ASSUME_TAC (RR[LESS_EQ_ADD] (SPECL["n:num";"n+n'"] 
     (MATCH_MP uchain_lemma (ASSUME "uchain (Q:num->^pred1)"))))
   THEN ASSUM_LIST (\thl. RT
     [MATCH_MP(MATCH_MP (el 2 thl) (PORR[implies_DEF] (el 1 thl))) (el 5 thl)])
   THEN ASSUME_TAC (RR[PORR[ADD_SYM]LESS_EQ_ADD] (SPECL["n':num";"n+n'"] 
     (MATCH_MP uchain_lemma (ASSUME "uchain (Q:num->^pred1)"))))
   THEN ASSUM_LIST (\thl. RT
     [MATCH_MP(MATCH_MP (el 4 thl) (PORR[implies_DEF] (el 1 thl))) (el 5 thl)])
  ;CONJ_TAC THEN EXISTS_TAC "n:num" THEN FIRST_ASSUM ACCEPT_TAC
  ]);;

% --- seq --- %
let t1 = TAC_PROOF
 (([],"uchain Q /\ monotonic (c':^ptrans23) ==> uchain(\n. c'(Q n))"),
  LPORT[uchain_DEF;monotonic_DEF] THEN REPEAT STRIP_TAC THEN
  BETA_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
  THEN STRIP_TAC THEN RES_TAC);;
let ucont_seq = TAC_PROOF
 (([],"ucontinuous (c:^ptrans23) /\ ucontinuous (c':^ptrans12)
       ==> ucontinuous (c seq c')"),
  LPORT[ucontinuous_DEF] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN PORT[seq_DEF] THEN ART[] THEN
  IMP_RES_TAC (PORR[ucontinuous_DEF] (DISCH_ALL (MATCH_MP ucont_mono
        (ASSUME "ucontinuous(c':^ptrans12)")))) THEN
  IMP_RES_TAC t1 THEN RES_TAC THEN ART[] THEN BETA_TAC THEN REFL_TAC);;

% --- cond --- %
let ucont_cond = prove
 ("ucontinuous (c:^ptrans12) /\ ucontinuous c'
       ==> ucontinuous (cond g c c')",
  LPORT[ucontinuous_DEF] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN PORT[cond_DEF] THEN ART[] THEN
  LPORT[or_DEF;and_DEF;not_DEF;ulimit_DEF] THEN FUN_TAC THEN EQ_TAC THENL
  [STRIP_TAC THEN EXISTS_TAC "n:num" THEN ART[]
  ;STRIP_TAC THEN ART[] THEN EXISTS_TAC "n:num" THEN ART[]
  ]);;

% --- do --- %
let lemma = TAC_PROOF
 (([],"monotonic c /\ uchain (Q:num->^pred) 
       ==> uchain (\n'. H g c n(Q n'))"),
  LPORT[monotonic_DEF;uchain_DEF] THEN STRIP_TAC
  THEN BETA_TAC THEN GEN_TAC
  THEN POP_ASSUM (ASSUME_TAC o SPEC "n':num") THEN
  IMP_RES_TAC (PORR[monotonic_DEF] mono_H)
  THEN POP_ASSUM MATCH_ACCEPT_TAC);;
let ucont_H =
 let t = TAUT "t==>t'==>t'' = t/\t'==>t''"
 in TAC_PROOF
  (([],"ucontinuous (c:^ptrans) ==> ucontinuous (H g c n)"),
   DISCH_THEN (\th. ASSUME_TAC (MATCH_MP ucont_mono th) THEN
   MP_TAC th) THEN PORT[ucontinuous_DEF] THEN REPEAT STRIP_TAC
   THEN SPEC_TAC("n:num","n:num") THEN INDUCT_TAC THENL
   [LPORT[H_DEF;ulimit_DEF;and_DEF;not_DEF] THEN FUN_TAC
    THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [EXISTS_TAC "n:num" THEN ART[]
    ;RES_TAC
    ;EXISTS_TAC "n:num" THEN POP_ASSUM ACCEPT_TAC
    ]
   ;PORT[H_DEF] THEN POP_ASSUM SUBST1_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (PORR[SYM t] lemma)) THEN
    RES_TAC THEN ART[] THEN
    LPORT[ulimit_DEF;and_DEF;or_DEF;not_DEF] THEN FUN_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[] THEN
    EXISTS_TAC "n':num" THEN ART[]
   ]);;
let ucont_do =
 let t = TAUT "t==>t'==>t'' = t/\t'==>t''"
 in TAC_PROOF
  (([],"ucontinuous (c:^ptrans) ==> ucontinuous (do g c)"),
   DISCH_TAC THEN LPORT[ucontinuous_DEF;UNDISCH do_bounded]
   THEN IMP_RES_TAC ucont_mono THEN GEN_TAC THEN DISCH_TAC 
   THEN PRT[ulimit_DEF] THEN REPEAT STRIP_TAC
   THEN FUN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SWAP_EXISTS_CONV THEN
    EXISTS_TAC "n:num" THEN POP_ASSUM MP_TAC THEN
    SUBST1_TAC (PORR[ulimit_DEF] (UNDISCH_ALL (SPEC_ALL
           (PORR[ucontinuous_DEF] (UNDISCH_ALL ucont_H)))))
    THEN BETA_TAC THEN DISCH_THEN ACCEPT_TAC
   ;STRIP_TAC THEN EXISTS_TAC "n':num" THEN
    SUBST1_TAC (SPEC "n':num" (GEN "n:num"(PORR[ulimit_DEF] (UNDISCH_ALL
      (SPEC_ALL (PORR[ucontinuous_DEF] (UNDISCH_ALL ucont_H)))))))
    THEN BETA_TAC THEN EXISTS_TAC "n:num" THEN POP_ASSUM ACCEPT_TAC
   ]);;

% --- abst --- %
let ucont_abst = TAC_PROOF
  (([],"ucontinuous (abst(r:^arel))"),
   LPORT[ucontinuous_DEF;ulimit_DEF;abst_DEF;uchain_DEF;implies_DEF] THEN
   REPEAT STRIP_TAC THEN FUN_TAC THEN PBETA_TAC THEN RT[] THEN EQ_TAC THEN 
   STRIP_TAC THENL
   [EXISTS_TAC "n:num" THEN EXISTS_TAC "a:*a" THEN ART[]
   ;EXISTS_TAC "a:*a" THEN ART[] THEN EXISTS_TAC "n:num" THEN ART[]
   ]);;



% --- continuity by bounded nondeterminism: nondass, block and dual-abst --- %

% --- nondass --- %
let t1 = TAC_PROOF
 (([],"(!n (v:*s1) . Q n v ==> Q (SUC n) v)
      ==> (!i j v. (i<=j) ==> Q i v ==> Q j v)"),
  PORT[LESS_OR_EQ] THEN REPEAT STRIP_TAC THENL
  [POP_ASSUM MP_TAC THEN POP_ASSUM (CHOOSE_TAC o MATCH_MP LESS_ADD)
   THEN POP_ASSUM (SUBST1_TAC o SYM) THEN SPEC_TAC("p:num","p:num")
   THEN INDUCT_TAC THENL
   [PORT[ADD] THEN DISCH_THEN ACCEPT_TAC
   ;EVERY_ASSUM (\th. ASSUME_TAC (SPEC "p+i" th ? th)) THEN
    PORT[ADD] THEN DISCH_TAC THEN RES_TAC THEN RES_TAC
   ]
  ;POP_ASSUM MP_TAC THEN ART[] THEN DISCH_THEN ACCEPT_TAC
  ]);;     
let t2 =
 let t = BETA_RULE
   (ISPECL["\(n:num).(Q n (v:*s1) :bool)";"n:num"] SELECT_AX)
 in TAC_PROOF
  (([],"!P.(!(v:*s1). P v ==> (?(n:num). Q n v))
           ==> ?N. !v. P v ==> Q (N v) v"),
   REPEAT STRIP_TAC THEN EXISTS_TAC "\(v:*s1). @(n:num). Q n v"
   THEN BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
   THEN IMP_RES_TAC t);;
let ucont_nondass =
 let t = TAC_PROOF(([],"m<n ==> m<=n"),DISCH_TAC THEN ART[LESS_OR_EQ])
 in let t' = TAC_PROOF(([],"(N:*s1->num)(f(i:num)) = (N o f)i"), 
    PORT[o_DEF] THEN BETA_TAC THEN RT[])
 in TAC_PROOF
  (([],"(!u. finite (\v. P u v))
         ==> ucontinuous (nondass P:^ptrans12)"),
   LPORT[finite_DEF;ucontinuous_DEF;ulimit_DEF;nondass_DEF;uchain_DEF;
         implies_DEF] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
   FUN_TAC THEN EQ_TAC THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM (MP_TAC o SPEC "x:*s2") THEN REPEAT 
    STRIP_TAC THEN IMP_RES_TAC t2 THEN 
    EXISTS_TAC "max ((N:*s1->num) o f) n" THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN POP_ASSUM (\th. POP_ASSUM MP_TAC THEN 
       POP_ASSUM (\th. ALL_TAC) THEN POP_ASSUM MP_TAC THEN RT[SYM th]) THEN
    PORT[t'] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC t THEN
    IMP_RES_TAC(SPEC"(N:*s1->num)o(f:num->*s1)"(GEN"N:num->num"max_prop)) THEN
    POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN IMP_RES_TAC t1
   ;REPEAT STRIP_TAC THEN EXISTS_TAC "n:num" THEN RES_TAC
   ]);;

% --- block --- %
let t1 = prove
 ("!p (c:^eptrans). block p c =
     (nondass \u(x,u').(u'=u) /\ p(x,u)) seq c seq (assign \(x,u).u)",
  REPEAT GEN_TAC THEN FUN_TAC THEN 
  LPRT[block_DEF;seq_DEF;nondass_DEF;assign_DEF] THEN FUN_TAC THEN
  PBETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [CONV_TAC(ONCE_DEPTH_CONV(PALPHA_CONV "(x:*,u:*s)")) THEN RT[] THEN
   RES_TAC THEN PORT[GSYM PAIR] THEN POART[] THEN ART[]
  ;POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o RR[] o SPEC"x':*,x:*s") THEN
   DISCH_TAC THEN RES_TAC THEN POP_ASSUM MP_TAC THEN
   CONV_TAC(ONCE_DEPTH_CONV(PALPHA_CONV "(x:*,u:*s)")) THEN RT[]
  ]);;
let ucont_block = prove
 ("!p. !c:^eptrans. ucontinuous c /\ (!u. finite (\x. p(x,u)))
     ==> ucontinuous (block p c)",
  REPEAT STRIP_TAC THEN RT[t1] THEN MATCH_MP_TAC ucont_seq THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC ucont_nondass THEN PBETA_TAC THEN GEN_TAC THEN
   POP_ASSUM (MP_TAC o SPEC_ALL) THEN PORT[finite_DEF] THEN
   BETA_TAC THEN STRIP_TAC THEN EXISTS_TAC "\m:num. (f m:*,u:*s)" THEN
   EXISTS_TAC "n:num" THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN
   EXISTS_TAC "i:num" THEN BETA_TAC THEN 
   PORT[GSYM PAIR] THEN POART[] THEN ART[]
  ;MATCH_MP_TAC ucont_seq THEN ART[ucont_assign]
  ]);;
 
% --- dualabst --- %
let dualabst_nondass = TAC_PROOF
 (([],"dual(abst(r:^arel)) = nondass(\(k,u)(a,u'). r(a,k,u) /\ (u'=u))"),
  FUN_TAC THEN LPORT[dual_abst;nondass_DEF] THEN FUN_TAC THEN PBETA_TAC THEN 
  RT[] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THENL
  [POP_ASSUM MP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN RT[]
  ;POP_ASSUM MP_TAC THEN POP_ASSUM (ASSUME_TAC o RR[] 
      o SPEC "(a:*a),SND(p:^cstate)") THEN POP_ASSUM ACCEPT_TAC
  ]);;
let ucont_dualabst = TAC_PROOF
  (([],"(!k u. finite (\a. r(a,k,u)))
         ==> ucontinuous (dual(abst(r:^arel)))"),
   DISCH_TAC THEN PORT[dualabst_nondass] THEN MATCH_MP_TAC ucont_nondass
   THEN PBETA_TAC THEN RT[]THEN GEN_TAC THEN
   POP_ASSUM (MP_TAC o SPECL["FST(u:^cstate)";"SND(u:^cstate)"]) THEN
   RT[finite_DEF] THEN BETA_TAC THEN STRIP_TAC THEN
   EXISTS_TAC "\(i:num).(f i:*a,SND(u:^cstate))" THEN EXISTS_TAC "n:num" THEN
   BETA_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN EXISTS_TAC "i:num" THEN
   ART[] THEN POP_ASSUM (\th.ALL_TAC) THEN POP_ASSUM (\th.ALL_TAC) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN RT[]);;


save_thm(`ucont_abort`,ucont_abort);;
save_thm(`ucont_skip`,ucont_skip);;
save_thm(`ucont_assign`,ucont_assign);;
save_thm(`ucont_dch`,ucont_dch);;
save_thm(`ucont_seq`,ucont_seq);;
save_thm(`ucont_cond`,ucont_cond);;
save_thm(`ucont_assert`,ucont_assert);;
save_thm(`ucont_guard`,ucont_guard);;
save_thm(`ucont_do`,ucont_do);;
save_thm(`ucont_abst`,ucont_abst);;
save_thm(`ucont_nondass`,ucont_nondass);;
save_thm(`ucont_block`,ucont_block);;
save_thm(`ucont_dualabst`,ucont_dualabst);;

