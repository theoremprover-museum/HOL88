
% A little modal logic of termination.

     HALTS p c = !s. p s ==> ?s'. c(s,s')
%

new_theory `halts`;;

load_library `string`;;
load_library `taut`;;

new_parent `semantics`;;

load_definitions `semantics`;;

new_parent `hoare_thms`;;

load_theorems `hoare_thms`;;


let HALTS =
 new_definition
  (`HALTS`,
   "HALTS p (c:state#state->bool) =
     !s. p s ==> ?s'. c(s,s')");;

let ASSIGN_HALTS =
 prove_thm
  (`ASSIGN_HALTS`,
   "!p x f. HALTS p (MK_ASSIGN(x,f))",
   REWRITE_TAC[HALTS;MK_ASSIGN]
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "BND(f s)x s"
    THEN REWRITE_TAC[]);;

% Proof rewritten for new RES_TAC:                        [TFM 90.04.27] %

let SEQ_HALTS =
 prove_thm
  (`SEQ_HALTS`,
   "!p c1 c2 q.
     HALTS p c1 /\ MK_SPEC(p,c1,q)  /\ HALTS q c2
     ==> HALTS p (MK_SEQ(c1,c2))",
   PURE_REWRITE_TAC[HALTS;MK_SEQ;MK_SPEC] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN RES_TAC THEN RES_TAC THEN
   MAP_EVERY EXISTS_TAC ["s''':state";"s':state"] THEN
   CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;


% Proof revised for Hol version 1.12     [TFM 91.01.24]         %
let IF1_HALTS =
 prove_thm
  (`IF1_HALTS`,
   "!p c b. HALTS (\s. p s /\ b s) c   ==> HALTS p (MK_IF1(b,c))",
   PURE_REWRITE_TAC[HALTS;MK_IF1] THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC "(b:state->bool)s" THEN
   ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC "s:state" THEN REFL_TAC]);;

% Proof revised for Hol version 1.12     [TFM 91.01.24]         %
let IF2_HALTS =
 prove_thm
  (`IF2_HALTS`,
   "!p c1 c2 b.
       HALTS (\s. p s /\ b s) c1 /\ HALTS (\s. p s /\ ~b s) c2
       ==> HALTS p (MK_IF2(b,c1,c2))",
   PURE_REWRITE_TAC[HALTS;MK_IF2] THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC "(b:state->bool)s" THEN
   ASM_REWRITE_TAC[] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let PRE_STRENGTH_HALTS =
 prove_thm
  (`PRE_STRENGTH_HALTS`,
   "!p p' c. (!s. p' s ==> p s) /\ HALTS p c ==> HALTS p' c",
   PURE_ONCE_REWRITE_TAC[HALTS] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    RES_TAC);;

% We now prove:

   "!b c x n.
     MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n) /\
     HALTS (\s. p s /\ b s) c
     ==> HALTS  p (MK_WHILE(b,c))"

  We assume that b never comes true and hence (in order to get a
  contradiction) construct a sequence s1, s2, s3, ...  of states such that

     c(s1,s2), c(s2,s3), c(s3,s4), ... etc.

  which we then map to an infinite decreasing sequence of numbers.
%

let DEC_SEQ =
 new_prim_rec_definition
  (`DEC_SEQ`,
   "(DEC_SEQ 0 (s:state) (c:state#state->bool) (b:state->bool) = s) /\
    (DEC_SEQ (SUC n) s c b =
      let y = DEC_SEQ n s c b in ((~(b y)) => y | @z. c(y,z)))");;

let SPEC_LEMMA1 =
 prove_thm
  (`SPEC_LEMMA1`,
   "(?x.!n.MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n)))
    ==>
    MK_SPEC((\s. p s /\ b s), c, p)",
   REWRITE_TAC[MK_SPEC]
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN ASSUM_LIST(\[th]. ASSUME_TAC(GEN "n:num" (SPEC_ALL th)))
    THEN ASSUM_LIST
          (\[th1;th2].ASSUME_TAC(REWRITE_RULE[](SPEC "(s1:state)x" th1)))
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let SEQ_LEMMA1 =
 prove_thm
  (`SEQ_LEMMA1`,
   "(!n. b(DEC_SEQ n s c b))            /\
    MK_SPEC((\s. p s /\ b s), c, p) /\
    HALTS (\s. p s /\ b s) c        /\
    p s
    ==>
    !m. p(DEC_SEQ m s c b) /\ c(DEC_SEQ m s c b, DEC_SEQ (SUC m) s c b)",
   PURE_REWRITE_TAC[MK_SPEC;HALTS] THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
   STRIP_TAC THEN INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THEN
   ASM_REWRITE_TAC [DEC_SEQ] THEN
   CONV_TAC (DEPTH_CONV let_CONV) THENL
   [FIRST_ASSUM (\th g. MP_TAC (SPEC "0" th) g) THEN
    PURE_ONCE_REWRITE_TAC [DEC_SEQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (\th g. ASSUME_TAC (SPEC "m:num" th) g) THEN
    CONJ_TAC THENL
    [RES_THEN (TRY o IMP_RES_THEN (CHECK_ASSUME_TAC o SELECT_RULE)) THEN
     RES_TAC;
     FIRST_ASSUM (\th g. MP_TAC (SPEC "SUC m" th) g) THEN
     PURE_ONCE_REWRITE_TAC [DEC_SEQ] THEN
     CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
     CONV_TAC SELECT_CONV THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     RES_THEN (TRY o IMP_RES_THEN (CHECK_ASSUME_TAC o SELECT_RULE)) THEN
     RES_TAC]]);;


let SEQ_LEMMA2 =
 prove_thm
  (`SEQ_LEMMA2`,
   "(!n. b(DEC_SEQ n s c b))                                                /\
    (?x.!n.MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) /\
    HALTS (\s. p s /\ b s) c                                                /\
    p s
    ==>
    ?x. !m. DEC_SEQ m s c b x > DEC_SEQ (SUC m) s c b x",
   REPEAT STRIP_TAC THEN
   EXISTS_TAC "x:string" THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC SPEC_LEMMA1 THEN
   IMP_RES_TAC SEQ_LEMMA1 THEN
   ASSUM_LIST
     (\thl.ASSUME_TAC(BETA_RULE(REWRITE_RULE[MK_SPEC](el 2(rev thl))))) THEN
   PURE_ONCE_REWRITE_TAC [GREATER] THEN
   ASSUM_LIST(\thl.ASSUME_TAC(SPEC"m:num"(hd(rev thl)))) THEN
   ASSUME_TAC (REFL "DEC_SEQ m s c b x") THEN
   EVERY_ASSUM (\th g. ASSUME_TAC (SPEC "m:num" th) g ? ALL_TAC g) THEN
   RES_TAC);;

let CONTRA_LEMMA = TAUT_PROVE "!t. t = (~t ==> F)";;

let WF_LEMMA =
 prove_thm
  (`WF_LEMMA`,
   "(!n. f n > f(SUC n)) ==> !n m. f m > n",
   REWRITE_TAC[GREATER]
    THEN STRIP_TAC
    THEN INDUCT_TAC
    THEN CONV_TAC(REWR_CONV CONTRA_LEMMA)
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THENL
     [REWRITE_TAC[NOT_LESS;LESS_OR_EQ;NOT_LESS_0]
      THEN STRIP_TAC
      THEN
       ASSUM_LIST
       (\[th1;th2].
          ASSUME_TAC(REWRITE_RULE[th1;GREATER;NOT_LESS_0](SPEC "m:num" th2)));
      ALL_TAC]
    THEN ASM_REWRITE_TAC[NOT_LESS;LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST(\[th1;th2;th3]. ASSUME_TAC(SPEC "m:num" th3))
    THEN ASSUM_LIST(\thl. ASSUME_TAC(SPEC "SUC m" (el 2 (rev thl))))
    THEN IMP_RES_TAC LESS_TRANS
    THEN IMP_RES_TAC LESS_LESS_SUC
    THEN ASSUM_LIST(\thl. ASSUME_TAC(SUBS[el 9 thl](el 8 thl)))
    THEN IMP_RES_TAC LESS_LESS_SUC);;

let WF_THM =
 prove_thm
  (`WF_THM`,
   "~?f. (!n. f n > f(SUC n))",
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC WF_LEMMA
    THEN ASSUM_LIST(\[th1;th2]. ASSUME_TAC(GEN_ALL(SPEC_ALL th1)))
    THEN POP_ASSUM
          (\th. ASSUME_TAC
                 (REWRITE_RULE
                   [LESS_REFL;GREATER]
                   (SPECL["m:num";"(f:num->num) m"]th)))
    THEN ASM_REWRITE_TAC[]);;

let lemma =
    let thm1 = CONV_RULE NOT_EXISTS_CONV WF_THM in
    let thm2 = SPEC "\m. DEC_SEQ m s c b(@x.!m.(DEC_SEQ m s c b x)
                        > (DEC_SEQ(SUC m)s c b x))" thm1 in
        CONV_RULE (ONCE_DEPTH_CONV BETA_CONV) thm2;;

let SEQ_LEMMA3 =
 prove_thm
  (`SEQ_LEMMA3`,
   "(?x.!n.MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) /\
    HALTS (\s. p s /\ b s) c                                                /\
    p s
    ==>
    ~(!n. b(DEC_SEQ n s c b))",
   REPEAT STRIP_TAC THEN
   REPEAT_GTCL IMP_RES_THEN (CHECK_ASSUME_TAC o SELECT_RULE) SEQ_LEMMA2 THEN
   IMP_RES_TAC lemma);;


let SEQ_LEMMA4 =
 prove_thm
  (`SEQ_LEMMA4`,
   "(?x.!n.MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) /\
    HALTS (\s. p s /\ b s) c                                                /\
    p s
    ==>
    ?n. ~b(DEC_SEQ n s c b)",
   DISCH_TAC
    THEN POP_ASSUM(\th. ASSUME_TAC(MP SEQ_LEMMA3 th))
    THEN POP_ASSUM(\th. ACCEPT_TAC(CONV_RULE NOT_FORALL_CONV th)));;

let SEQ_LEMMA5 =
 prove_thm
  (`SEQ_LEMMA5`,
   "(?x.!n.MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) /\
    HALTS (\s. p s /\ b s) c                                                /\
    p s
    ==>
    ?n. ~b(DEC_SEQ n s c b) /\ !m. (m < n) ==> b(DEC_SEQ m s c b)",
   DISCH_TAC
    THEN POP_ASSUM(\th. ASSUME_TAC(MP SEQ_LEMMA4 th))
    THEN POP_ASSUM
          (\th. ASSUME_TAC
                 (MP (BETA_RULE(SPEC "\n.~b(DEC_SEQ n s c b)" WOP)) th))
    THEN POP_ASSUM(\th. ACCEPT_TAC(REWRITE_RULE [] th)));;

let MK_FINITE_WHILE = definition `semantics` `MK_FINITE_WHILE`;;


let SEQ_LEMMA6 =
 prove_thm
  (`SEQ_LEMMA6`,
   "!n. DEC_SEQ n (DEC_SEQ (SUC 0) s c b) c b = DEC_SEQ (SUC n) s c b",
   REWRITE_TAC[DEC_SEQ;LET_DEF]
    THEN BETA_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[DEC_SEQ;LET_DEF]
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[]);;

% The following proof modified for Version 1.12 resolution  [TFM 91.01.25] %

let SEQ_LEMMA7 =
 prove_thm
  (`SEQ_LEMMA7`,
   "MK_SPEC((\s. p s /\ b s), c, p) /\
    HALTS (\s. p s /\ b s) c
    ==>
    !n s.
     p s /\ ~b(DEC_SEQ n s c b) /\ (!m. (m < n) ==> b(DEC_SEQ m s c b))
     ==>
     MK_FINITE_WHILE (SUC n) (b,c) (s, DEC_SEQ n s c b)",
   PURE_REWRITE_TAC[HALTS;MK_SPEC] THEN
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
   STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;DEC_SEQ;NOT_LESS_0;MK_IF1]
    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;MK_IF1] THEN
    ASSUM_LIST
     (\thl. ASSUME_TAC(REWRITE_RULE[LESS_0;DEC_SEQ](SPEC "0" (el 1 thl)))) THEN
    ASM_REWRITE_TAC[MK_SEQ] THEN
    EXISTS_TAC "DEC_SEQ (SUC 0) s c b" THEN
    let th = ASSUME
        "!s:string->num. p s /\ b s ==> (?s':string->num. c(s,s'))" in
    IMP_RES_THEN (IMP_RES_THEN (CHECK_ASSUME_TAC o SELECT_RULE)) th THEN
    ASSUME_TAC
       (REWRITE_RULE
            [ASSUME "(b:state->bool)s"]
            (SYM
              (BETA_RULE
               (REWRITE_RULE
                 [LET_DEF;CONJUNCT1 DEC_SEQ]
                 (INST["0","n:num"](SPEC_ALL(CONJUNCT2 DEC_SEQ))))))) THEN
    ASSUM_LIST(\thl. ASSUME_TAC(REWRITE_RULE[el 1 thl](el 2 thl))) THEN
    POP_ASSUM(\th. REWRITE_TAC[th]) THEN
    ONCE_REWRITE_TAC[SYM(SPEC_ALL SEQ_LEMMA6)] THEN
    REWRITE_TAC[CONJUNCT1 DEC_SEQ] THEN
    ASSUM_LIST(\thl. IMP_RES_TAC(el 1 (rev thl))) THEN
    ASSUM_LIST(\thl. ASSUME_TAC(REWRITE_RULE[el 2 thl](el 1 thl))) THEN
    ASSUM_LIST
       (\thl. ASSUME_TAC(SUBS[SYM(SPEC_ALL SEQ_LEMMA6)](el 7 thl))) THEN
    ASSUM_LIST
         (\thl.
           ASSUME_TAC
            (GEN
             "m:num"
             (REWRITE_RULE[LESS_MONO_EQ](SPEC "SUC m" (el 7 thl))))) THEN
    POP_ASSUM
          (\th. ASSUME_TAC(ONCE_REWRITE_RULE[SYM(SPEC_ALL SEQ_LEMMA6)]th))
    THEN RES_TAC]);;

% The following proof modified for Version 1.12 resolution  [TFM 91.01.25] %

let WHILE_HALTS =
 prove_thm
  (`WHILE_HALTS`,
   "!b c x.
     (!n. MK_SPEC((\s. p s /\ b s /\ (s x = n)), c, (\s. p s /\ s x < n))) /\
     HALTS (\s. p s /\ b s) c
     ==> HALTS  p (MK_WHILE(b,c))",
   REPEAT STRIP_TAC THEN REWRITE_TAC[HALTS] THEN
   X_GEN_TAC "s:state" THEN STRIP_TAC THEN
   IMP_RES_TAC SPEC_LEMMA1 THEN
   let th = UNDISCH_ALL (hd(IMP_CANON SEQ_LEMMA5)) in
   STRIP_ASSUME_TAC (SELECT_RULE th) THEN
   IMP_RES_TAC SEQ_LEMMA7 THEN
   REWRITE_TAC[MK_WHILE] THEN
   EXISTS_TAC
    "DEC_SEQ(@n.~b(DEC_SEQ n s c b) /\ (!m.m<n ==> b(DEC_SEQ m s c b)))s c b"
   THEN EXISTS_TAC
        "SUC(@n.~b(DEC_SEQ n s c b) /\ (!m.m<n ==> b(DEC_SEQ m s c b)))"
   THEN ASM_REWRITE_TAC[]);;

