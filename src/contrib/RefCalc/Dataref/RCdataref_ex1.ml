% File: RCdataref_ex1.ml %

% An example action system data refinement %

% NB: Since this example requires the more_lists library and it
      defines a new function (seqlist) you may want to make it
      a separate theory, with RCdataref as a parent %

load_library `more_lists`;;

% "seqlist f n" is the list "[f 0;..;f(n-1)]" %
let seqlist_DEF = new_prim_rec_definition(`seqlist_DEF`,
  "(seqlist (f:num->num) 0 = []) /\
   (seqlist f (SUC n) = APPEND (seqlist f n) [f n])");;


% --- prove a few lemmas about seqlist --- %

let length_append1 = TAC_PROOF
 (([],"!l (x:*). LENGTH (APPEND l [x]) = SUC(LENGTH l)"),
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [GEN_TAC THEN LPORT[APPEND;LENGTH;LENGTH] THEN REFL_TAC
  ;GEN_TAC THEN GEN_TAC THEN LPORT[APPEND;LENGTH] THEN ART[]
  ]);;
let length_seqlist = TAC_PROOF
 (([],"!n. LENGTH (seqlist f n) = n"),
  INDUCT_TAC THENL
  [LPORT[seqlist_DEF;LENGTH;LENGTH] THEN REFL_TAC
  ;LPORT[seqlist_DEF;length_append1] THEN ART[]
  ]);;

let null_nil = prove("!l. NULL(l:(*)list) = (l=[])",
  INDUCT_THEN list_INDUCT ASSUME_TAC THENL
  [RT[C1 NULL]
  ;LRT[C2 NULL;NOT_CONS_NIL]
  ]);;
let seqlist_notnull = TAC_PROOF
 (([],"!n. 0<n ==> ~(seqlist f n = [])"),
  INDUCT_TAC THENL
  [RT[NOT_LESS_0]
  ;LRT[seqlist_DEF;PORR[null_nil]APPEND_IS_NULL;PORR[EQ_SYM_EQ]NOT_NIL_CONS]
  ]);;
let hd_seqlist_suc = 
 let t01 = RR[LESS_0] (IMP_TRANS (SPEC "SUC n" seqlist_notnull)
           (ISPEC "seqlist f(SUC n)" HD_APPEND)) in
 prove("!n. HD(seqlist f(SUC n)) = f 0",
  PORT[seqlist_DEF] THEN INDUCT_TAC THENL
  [LRT[seqlist_DEF;APPEND;HD]
  ;LPORT[t01;seqlist_DEF] THEN FIRST_ASSUM ACCEPT_TAC
  ]);;
let hd_seqlist = TAC_PROOF
 (([],"!n. 0<n ==> (HD (seqlist f n) = f 0)"),
  GEN_TAC THEN DISJ_CASES_TAC (SPEC "n:num" num_CASES) THENL
  [ART[NOT_LESS_0]
  ;POP_ASSUM MP_TAC THEN REPEAT STRIP_TAC THEN ART[hd_seqlist_suc]
  ]);;

let seqlist_last =
 let t02 = PORR[HD] (RHS_ORR1 (C1 EL) 
         (LRR[SPEC_ALL length_seqlist;LESS_EQ_REFL;SUB_EQUAL_0]
         (ISPECL["seqlist f n";"[(f:num->num)n]";"n:num"] EL_APPEND_2))) in
 prove("!n. EL n (seqlist f (SUC n)) = f n",LRT[seqlist_DEF;t02]);;
let seqlist_prop = 
 let t = prove("(m<SUC n) = (m<=n)",
           PORT[LESS_THM;LESS_OR_EQ] THEN LHS_ORT1 DISJ_SYM THEN REFL_TAC) in
 let t03 = LRR[SPEC_ALL length_seqlist;t]
           (ISPECL["seqlist f n";"[(f:num->num)n]";"j:num"] EL_APPEND_1) in
 prove("!n j.j<n ==> (EL j (seqlist f n) = f j)",
  INDUCT_TAC THENL
  [ART[NOT_LESS_0]
  ;GEN_TAC THEN PORT[LESS_THM] THEN STRIP_TAC THENL
   [ART[seqlist_last]
   ;RES_TAC THEN IMP_RES_TAC t03 THEN ART[seqlist_DEF]
  ]]);;


% --- a lemma which should have been found in a library? --- %

let el_tl = 
 let t = LRR[EL1;LESS_0](SPEC "SUC n" EL1_SUC_CONS) in
 prove("!(l:(*)list). ~(l=[]) ==> (EL j(TL l) = EL(SUC j)l)",
   GEN_TAC THEN DISJ_CASES_TAC (ISPEC "l:(*)list" list_CASES) THEN ART[]
   THEN POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC
   THEN LRT[TL;t]);;


% --- the example: a simple max calculation --- %

let AINIT  = "\((a:num,i),m). (a = f 0) /\ (i = 0) /\ (m = 0)";;
let AACT1 = "(\((a,i),m). (i < n) /\ (m < a)),
             (assign \((a:num,i),m:num). ((f(SUC i):num,SUC i),a))";;
let AACT2 = "(\((a,i),m). (i < n) /\ (a <= m)),
             (assign \((a:num,i),m:num). ((f(SUC i):num,SUC i),m))";;

let CINIT  = "\(c:(num)list,m). (c = seqlist f n) /\ (m = 0)";;
let CACT1 = "(\(c,m). ~(c = []) /\ (m < HD c)),
             (assign \(c:(num)list,m:num). (TL c,HD c))";;
let CACT2 = "(\(c,m). ~(c = []) /\ (HD c <= m)),
             (assign \(c:(num)list,m:num). (TL c,m))";;


let ASYS = "block ^AINIT (ldo[^AACT1;^AACT2])";;
let CSYS = "block ^CINIT (ldo[^CACT1;^CACT2])";;

let R = "\((a:num,i),c,m:num).
      (i<n ==> (a = HD c)) /\
      (n = LENGTH c + i) /\
      (!j. ((i+j)<n) ==> (EL j c = f (i+j)))";;


% --- lemma: merging guard into demonic assignment --- %

let grd_seq_nondass = prove
 ("(guard b) seq (nondass(P:*s1->*s2->bool)) 
        = nondass (\v v'. b v /\ P v v')",
   FUN_TAC THEN LPRT[seq_DEF;guard_DEF;imp_DEF;nondass_DEF] THEN FUN_TAC THEN 
   EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ART[]);;

let th1 = TAUT "t/\t'\/t/\t'' = t/\(t'\/t'')";;

% --- the proof --- %

goal "^ASYS ref ^CSYS";;
e(MATCH_MP_TAC actsys_dataref THEN EXISTS_TAC R THEN
  LRT[LENGTH;EVERY_DEF;EVERY2;TL;HD] THEN PBETA_TAC THEN REPEAT CONJ_TAC);;
%1%e(EVERY_MAPSND_mono_TAC);;
%2%e(REPEAT STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN POP_ASSUM SUBST1_TAC
      THEN EXISTS_TAC "(f:num->num)0,0" THEN PBETA_TAC
      THEN RT[ADD_CLAUSES;length_seqlist;seqlist_prop]
      THEN DISCH_TAC THEN IMP_RES_TAC hd_seqlist THEN ART[]);;
%3%e(LPORT[assign_eq_nondass;grd_seq_nondass] THEN 
     MATCH_MP_TAC nondass_dataref THEN PBETA_TAC THEN
     P_PGEN_TAC "(a:num,i:num)" THEN REPEAT GEN_TAC THEN RT[PAIR_EQ] THEN
     STRIP_TAC THEN EXISTS_TAC "f(SUC i):num,SUC i" THEN ART[PAIR_EQ] THEN
     REPEAT (POP_ASSUM MP_TAC) THEN
     CASE_TAC "k:(num)list" list_CASES [NOT_CONS_NIL;HD;TL;LENGTH] THEN
     LRT[ADD_CLAUSES;LESS_MONO_EQ] THEN REPEAT STRIP_TAC THENL
     [ASSUM_LIST(\l.MP_TAC(SPEC"1"(el 5 l))) THEN 
      ASSUM_LIST(\l.SUBST1_TAC(el 6 l)) THEN
      LRT[GSYM ADD1;num_CONV"1";EL;TL;HD;LESS_MONO_EQ] THEN STRIP_TAC THEN
      RES_TAC THEN ART[]
     ;ASSUM_LIST(\l.MP_TAC(SPEC"SUC j"(el 5 l))) THEN
      ASSUM_LIST(\l.SUBST1_TAC(el 6 l)) THEN LRT[EL;TL;HD;ADD_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ART[LESS_MONO_EQ]
     ;PORT[EQ_SYM_EQ] THEN FIRST_ASSUM MATCH_MP_TAC THEN ART[] THEN
      MATCH_ACCEPT_TAC(LPORR[ADD_CLAUSES;ADD_SYM] LESS_ADD_SUC)
     ]);;
%4%e(LPORT[assign_eq_nondass;grd_seq_nondass] THEN 
     MATCH_MP_TAC nondass_dataref THEN PBETA_TAC THEN
     P_PGEN_TAC "(a:num,i:num)" THEN REPEAT GEN_TAC THEN RT[PAIR_EQ] THEN
     STRIP_TAC THEN EXISTS_TAC "f(SUC i):num,SUC i" THEN ART[PAIR_EQ] THEN
     REPEAT (POP_ASSUM MP_TAC) THEN
     CASE_TAC "k:(num)list" list_CASES [NOT_CONS_NIL;HD;TL;LENGTH] THEN
     LRT[ADD_CLAUSES;LESS_MONO_EQ] THEN REPEAT STRIP_TAC THENL
     [ASSUM_LIST(\l.MP_TAC(SPEC"1"(el 5 l))) THEN 
      ASSUM_LIST(\l.SUBST1_TAC(el 6 l)) THEN
      LRT[GSYM ADD1;num_CONV"1";EL;TL;HD;LESS_MONO_EQ] THEN STRIP_TAC THEN
      RES_TAC THEN ART[]
     ;ASSUM_LIST(\l.MP_TAC(SPEC"SUC j"(el 5 l))) THEN
      ASSUM_LIST(\l.SUBST1_TAC(el 6 l)) THEN LRT[EL;TL;HD;ADD_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ART[LESS_MONO_EQ]
     ]);;
%5%e(P_PGEN_TAC "(a:num,i:num)" THEN REPEAT GEN_TAC THEN PBETA_TAC THEN
     RT[] THEN CASE_TAC "k:(num)list" list_CASES [NOT_CONS_NIL;HD;LENGTH] THEN
     STRIP_TAC THEN SUBGOAL_THEN "i<n" ASSUME_TAC THENL
     [ART[] THEN MATCH_ACCEPT_TAC(LPORR[ADD_SYM] LESS_ADD_SUC)
     ;RES_TAC THEN ART[]
     ]);;
%6%e(P_PGEN_TAC "(a:num,i:num)" THEN REPEAT GEN_TAC THEN PBETA_TAC THEN
     RT[] THEN CASE_TAC "k:(num)list" list_CASES [NOT_CONS_NIL;HD;LENGTH] THEN
     STRIP_TAC THEN SUBGOAL_THEN "i<n" ASSUME_TAC THENL
     [ART[] THEN MATCH_ACCEPT_TAC(LPORR[ADD_SYM] LESS_ADD_SUC)
     ;RES_TAC THEN ART[]
     ]);;    
%7%e(LRT[lguard_DEF;or_DEF;false_DEF] THEN P_PGEN_TAC "(a:num,i:num)" THEN
     REPEAT GEN_TAC THEN PBETA_TAC THEN LRT[th1;LESS_CASES] THEN
     REPEAT STRIP_TAC THEN UNDISCH_TAC "n=(LENGTH(k:(num)list))+i" THEN
     ART[LENGTH;ADD_CLAUSES] THEN STRIP_TAC THEN UNDISCH_TAC "i<n" THEN
     ART[LESS_REFL]);;

let theorem = top_thm();;
