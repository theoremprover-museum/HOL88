
% Proof of theorems corresponding to the Hoare rules and axioms %

new_theory `hoare_thms`;;

load_library `string`;;

new_parent `semantics`;;

load_definitions `semantics`;;
load_theorems    `semantics`;;

let ASSIGN_THM =
 prove_thm
  (`ASSIGN_THM`,
   "!p x f. MK_SPEC((\s. p (BND (f s) x s)), MK_ASSIGN(x,f), p)",
   REWRITE_TAC[MK_SPEC;MK_ASSIGN;BND]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST(\[th1;th2]. ACCEPT_TAC(SUBS[SYM th1]th2)));;

% Two useful theorems about BND that are used by ASSIGN_AX %

let BND_THM1 =
 prove_thm
  (`BND_THM1`,
   "!e x s. BND e x s x = e",
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REWRITE_TAC[]);;

let BND_THM2 =
 prove_thm
  (`BND_THM2`,
   "!e x s y. ~(y = x) ==> (BND e x s y = (s y))",
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]);;

let SEQ_THM =
 prove_thm
  (`SEQ_THM`,
   "!p q r c1 c2.
    MK_SPEC(p,c1,q) /\ MK_SPEC(q,c2,r) ==> MK_SPEC(p,MK_SEQ(c1,c2),r)",
   REWRITE_TAC[MK_SPEC;MK_SEQ]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN RES_TAC);;

% Proof revised for HOL version 1.12 [TFM 91.01.24]			%

let IF1_THM =
 prove_thm
  (`IF1_THM`,
   "!p q c b.
     MK_SPEC((\s. p s /\ b s),c,q) /\ (!s. p s /\ ~(b s) ==> q s) ==>
     MK_SPEC(p,MK_IF1(b,c),q)",
   REWRITE_TAC[MK_SPEC;MK_IF1] THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC "(b:state->bool)s1" THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THENL
   [RES_TAC;
    FIRST_ASSUM (\th g. SUBST1_TAC (SYM th) g) THEN RES_TAC]);;

let IF2_THM =
 prove_thm
  (`IF2_THM`,
   "!p q c1 c2 b.
     MK_SPEC((\s. p s /\ b s),c1,q) /\ MK_SPEC((\s. p s /\ ~(b s)),c2,q) ==>
     MK_SPEC(p,MK_IF2(b,c1,c2),q)",
   REWRITE_TAC[MK_SPEC;MK_IF2]
    THEN REPEAT GEN_TAC
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s1"
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let PRE_STRENGTH_THM =
 prove_thm
  (`PRE_STRENGTH_THM`,
   "!p p' q c.
     (!s. p' s ==> p s) /\ MK_SPEC(p,c,q) ==> MK_SPEC(p',c,q)",
   REWRITE_TAC[MK_SPEC]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN RES_TAC);;

let POST_WEAK_THM =
 prove_thm
  (`POST_WEAK_THM`,
   "!p q q' c.
     MK_SPEC(p,c,q)/\ (!s. q s ==> q' s)  ==> MK_SPEC(p,c,q')",
   REWRITE_TAC[MK_SPEC]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN RES_TAC);;

let MK_FINITE_WHILE_CLAUSES =
 prove_thm
  (`MK_FINITE_WHILE_CLAUSES`,
   "(MK_FINITE_WHILE 0       (p,c) (s,s')  =  F) /\
    (MK_FINITE_WHILE (SUC n) (p,c) (s,s')  =  
      MK_IF1(p, MK_SEQ(c, MK_FINITE_WHILE n (p,c))) (s,s'))",
   PURE_REWRITE_TAC[MK_FINITE_WHILE]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[]);;

let WHILE_THM =
 prove_thm
  (`WHILE_THM`,
   "!p c b.
     MK_SPEC((\s. p s /\ b s),c,p) ==> 
     MK_SPEC(p,MK_WHILE(b,c),(\s. p s /\ ~(b s)))",
    REWRITE_TAC[MK_SPEC;MK_WHILE] 
     THEN BETA_TAC
     THEN REPEAT GEN_TAC
     THEN STRIP_TAC
     THEN REPEAT GEN_TAC
     THEN STRIP_TAC
     THEN ASSUM_LIST(\thl. UNDISCH_TAC(concl(hd thl)))
     THEN ASSUM_LIST(\thl. UNDISCH_TAC(concl(hd thl)))
     THEN SPEC_TAC("s2:state","s2:state")
     THEN SPEC_TAC("s1:state","s1:state")
     THEN SPEC_TAC("n:num","n:num")
     THEN INDUCT_TAC
     THEN REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;MK_IF1;MK_SEQ]
     THEN REPEAT GEN_TAC
     THEN ASM_CASES_TAC "(b:state->bool)s1"
     THEN ASM_REWRITE_TAC[]
     THEN STRIP_TAC
     THEN STRIP_TAC
     THEN RES_TAC
     THEN RES_TAC
     THEN ASM_REWRITE_TAC[]
     THEN ASSUM_LIST(\thl. SUBST_TAC[SYM(el 4 thl)])
     THEN ASM_REWRITE_TAC[]);;

close_theory();;
