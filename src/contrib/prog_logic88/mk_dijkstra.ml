% Definition of weakest preconditions in HOL %

new_theory `dijkstra`;;

load_library `string`;;

new_parent `halts_thms`;;

load_definition `halts` `HALTS`;;

load_definitions `halts_thms`;;
load_definitions `semantics`;;

% If p and p' are predicates then "p' is weaker then p" if
  p' is "less constraining", i.e. everything satisfying p also
  satisfies p', but perhaps there are some things satisfying p'
  that do not satisfy p.
%

let WEAKER =
 new_definition
  (`WEAKER`,
   "WEAKER p' p = !s:*. p s ==> p' s");;

let WEAKER_ANTISYM =
 prove_thm
  (`WEAKER_ANTISYM`,
   "!p1 p2 : *->bool. WEAKER p1 p2 /\ WEAKER p2 p1 ==> (p1=p2)",
   REWRITE_TAC[WEAKER]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

% Uniqueness of weakest conditions %

let WEAKEST_UNIQUE_LEMMA =
 prove_thm
  (`WEAKEST_UNIQUE_LEMMA`,
   "!P:(*->bool)->bool. !p1 p2.
     (P p1 /\ !p'. P p' ==> WEAKER p1 p') /\
     (P p2 /\ !p'. P p' ==> WEAKER p2 p') ==>
     (p1 = p2)",
   REPEAT STRIP_TAC
    THEN RES_TAC
    THEN IMP_RES_TAC WEAKER_ANTISYM);;


% The weakest thing satisfying P is a predicate p satisfying
  P that is weaker than all other predicated satisfying P.
%

let WEAKEST =
 new_definition
  (`WEAKEST`,
   "WEAKEST(P:(*->bool)->bool) =
     @p. P p /\ !p'. P p' ==> WEAKER p p'");;

% Uniqueness of WEAKEST %

let WEAKEST_UNIQUE =
 prove_thm
  (`WEAKEST_UNIQUE`,
   "!P:(*->bool)->bool. !p.
     (P p /\ !p'. P p' ==> WEAKER p p') ==> (p = WEAKEST P)",
   REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN ASSUM_LIST
          (\[th].
            let t = concl th
            and p = "p:*->bool"
            in
            ASSUME_TAC(SELECT_RULE(EXISTS("?^p.^t",p)th)))
    THEN ASSUM_LIST % Why doesn't IMP_RES_TAC work? %
          (\[th1;th2].
             ASSUME_TAC(MATCH_MP WEAKEST_UNIQUE_LEMMA (CONJ th1 th2)))
    THEN ASM_REWRITE_TAC[WEAKEST]);;

% Abstract definition of weakest precondition %

let WP =
 new_definition
  (`WP`,
   "WP (c,q) = WEAKEST(\p. T_SPEC(p,c,q))");;

% Abstract definition of weakest liberal precondition %

let WLP =
 new_definition
  (`WLP`,
   "WLP (c,q) = WEAKEST(\p. MK_SPEC(p,c,q))");;


% Alternative definitions (corresponds to the definition on page 88 of
  Backhouse's book or page 108 of Gries' book).
%

let WP1 =
 new_definition
  (`WP1`,
   "WP1 (c,q) (s:state) =
     (?s':state. c(s,s')) /\ (!s'. c(s,s') ==> q s')");;

let WLP1 =
 new_definition
  (`WLP1`,
   "WLP1 (c,q) (s:state) = !s':state. c(s,s') ==> q s'");;

let WP1_T_SPEC =
 prove_thm
  (`WP1_T_SPEC`,
   "!c q. T_SPEC(WP1(c,q),c,q)",
   REWRITE_TAC[WP1;T_SPEC;HALTS;MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC "s':state"
    THEN ASM_REWRITE_TAC[]);;

let WLP1_MK_SPEC =
 prove_thm
  (`WLP1_MK_SPEC`,
   "!c q. MK_SPEC(WLP1(c,q),c,q)",
   REWRITE_TAC[WLP1;MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let WP1_WEAKEST =
 prove_thm
  (`WP1_WEAKEST`,
   "!p c q. T_SPEC(p,c,q) ==> WEAKER (WP1(c,q)) p",
   REWRITE_TAC[WEAKER;WP1;T_SPEC;HALTS;MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;RES_TAC]);;

let WLP1_WEAKEST =
 prove_thm
  (`WLP1_WEAKEST`,
   "!p c q. MK_SPEC(p,c,q) ==> WEAKER (WLP1(c,q)) p",
   REWRITE_TAC[WEAKER;WLP1;MK_SPEC]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let WP1_LEMMA =
 MATCH_MP
  (BETA_RULE
    (SPEC "\p. T_SPEC(p,c,q)" (INST_TYPE [":state", ":*"] WEAKEST_UNIQUE)))
  (CONJ (SPEC_ALL WP1_T_SPEC) (GEN "p:state->bool" (SPEC_ALL WP1_WEAKEST)));;

let WLP1_LEMMA =
 MATCH_MP
  (BETA_RULE
    (SPEC "\p. MK_SPEC(p,c,q)" (INST_TYPE [":state", ":*"] WEAKEST_UNIQUE)))
  (CONJ (SPEC_ALL WLP1_MK_SPEC) (GEN "p:state->bool" (SPEC_ALL WLP1_WEAKEST)));;

let WP_WP1 =
 prove_thm
  (`WP_WP1`,
   "!c q. WP (c,q) = WP1 (c,q)",
   REWRITE_TAC[WP1_LEMMA;WP]);;

let WLP_WLP1 =
 prove_thm
  (`WLP_WLP1`,
   "!c q. WLP (c,q) = WLP1 (c,q)",
   REWRITE_TAC[WLP1_LEMMA;WLP]);;

let WP_THM =
 prove_thm
  (`WP_THM`,
   "!c q. WP (c,q) = \s. (?s':state. c(s,s')) /\ (!s'. c(s,s') ==> q s')",
    REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REWRITE_TAC[WP_WP1;WP1]);;

let WLP_THM =
 prove_thm
  (`WLP_THM`,
   "!c q. WLP (c,q) = \s.!s'. c(s,s') ==> q s'",
   REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REWRITE_TAC[WLP_WLP1;WLP1]);;

let WP_T_SPEC =
 prove_thm
  (`WP_T_SPEC`,
  "!c q. (?s. WP(c,q)s) ==> T_SPEC(WP(c,q),c,q)",
   REWRITE_TAC[WP_WP1;WP1_T_SPEC]);;

let WLP_MK_SPEC =
 prove_thm
  (`WLP_MK_SPEC`,
  "!c q. (?s. WLP(c,q)s) ==> MK_SPEC(WLP(c,q),c,q)",
   REWRITE_TAC[WLP_WLP1;WLP1_MK_SPEC]);;

let WP_WEAKEST =
 prove_thm
  (`WP_WEAKEST`,
   "!p c q. T_SPEC(p,c,q) ==> WEAKER (WP(c,q)) p",
   REWRITE_TAC[WP_WP1;WP1_WEAKEST]);;

let WLP_WEAKEST =
 prove_thm
  (`WLP_WEAKEST`,
   "!p c q. MK_SPEC(p,c,q) ==> WEAKER (WLP(c,q)) p",
   REWRITE_TAC[WLP_WLP1;WLP1_WEAKEST]);;

let T_SPEC_WP =
 prove_thm
  (`T_SPEC_WP`,
   "!p c q. T_SPEC(p,c,q) = !s. (p s ==> WP(c,q)s)",
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC THENL
    [IMP_RES_THEN MP_TAC WP_WEAKEST THEN
     PURE_ONCE_REWRITE_TAC[WEAKER] THEN DISCH_TAC THEN RES_TAC;
     REWRITE_TAC[WP_THM;T_SPEC;MK_SPEC;HALTS] THEN
     POP_ASSUM(ASSUME_TAC o BETA_RULE o REWRITE_RULE[WP_THM]) THEN
     REPEAT STRIP_TAC THENL
     [RES_TAC; RES_THEN MATCH_ACCEPT_TAC]]);;

let MK_SPEC_WLP =
 prove_thm
  (`MK_SPEC_WLP`,
   "!p c q. MK_SPEC(p,c,q) = !s. (p s ==> WLP(c,q)s)",
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC WLP_WEAKEST
    THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[WEAKER])
    THEN RES_TAC
    THEN REWRITE_TAC[WLP_THM;MK_SPEC]
    THEN POP_ASSUM(ASSUME_TAC o BETA_RULE o REWRITE_RULE[WLP_THM])
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

% Dijkstra's properties 1 -- 4 (see pp 18-19 of his book). %

let WP_PROP1 =
 prove_thm
  (`WP_PROP1`,
   "!c. WP(c, \s.F) = \s.F",
   REWRITE_TAC[WP_THM]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let WLP_PROP1 =
 prove_thm
  (`WLP_PROP1`,
   "!c. WLP(c, \s.F) = \s. ~?s'. c(s,s')",
   REWRITE_TAC[WLP_THM]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[]);;

let WP_PROP2 =
 prove_thm
  (`WP_PROP2`,
   "!p q c. (!s. p s ==> q s) ==> !s. WP(c,p)s ==> WP(c,q)s",
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC THENL
    [EXISTS_TAC "s':state" THEN ASM_REWRITE_TAC[];RES_TAC THEN RES_TAC]);;


let WLP_PROP2 =
 prove_thm
  (`WLP_PROP2`,
   "!p q c. (!s. p s ==> q s) ==> !s. WLP(c,p)s ==> WLP(c,q)s",
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC THEN RES_TAC);;

let WP_PROP3 =
 prove_thm
  (`WP_PROP3`,
   "!p q c s. WP(c,p)s /\ WP(c,q)s = WP(c, \s. p s /\ q s)s",
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC "s':state"
    THEN ASM_REWRITE_TAC[]);;

let WLP_PROP3 =
 prove_thm
  (`WLP_PROP3`,
   "!p q c s. WLP(c,p)s /\ WLP(c,q)s = WLP(c, \s. p s /\ q s)s",
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let WP_PROP4 =
 prove_thm
  (`WP_PROP4`,
   "!p q c s. WP(c,p)s \/ WP(c,q)s ==> WP(c, \s. p s \/ q s)s",
   REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN (EXISTS_TAC "s':state" ORELSE ALL_TAC)
    THEN ASM_REWRITE_TAC[]);;

let WLP_PROP4 =
 prove_thm
  (`WLP_PROP4`,
   "!p q c s. WLP(c,p)s \/ WLP(c,q)s ==> WLP(c, \s. p s \/ q s)s",
   REWRITE_TAC[WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;

% DISJ1_TAC                 DISJ2_TAC

   u \/ v                    u \/ v
   ======                    ======
     u                         v
%

let WP_PROP4' =
 prove_thm
  (`WP_PROP4'`,
   "!p q c. DET c ==> !s:state. WP(c,p)s \/ WP(c,q)s = WP(c, \s. p s \/ q s)s",
   REWRITE_TAC[DET] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN
   REWRITE_TAC[WP_PROP4;WP_THM] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL
    [EXISTS_TAC "s':state" THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    RES_THEN (REPEAT_GTCL IMP_RES_THEN (TRY o SUBST1_TAC)) THEN
    FIRST_ASSUM ACCEPT_TAC];
    DISJ2_TAC THEN CONJ_TAC THENL
    [EXISTS_TAC "s':state" THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    RES_THEN (REPEAT_GTCL IMP_RES_THEN (TRY o SUBST1_TAC)) THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

load_library `taut`;;

let DISJ_IMP_LEMMA =
 TAUT_PROVE
 "!t1 t2. (t1 \/ t2) = (~t2 ==> t1)";;

let NOT_IMP_LEMMA =
 TAUT_PROVE
 "!t1 t2. ~(t1 ==> t2) = (t1 /\ ~t2)";;

let WLP_PROP4' =
 prove_thm
  (`WLP_PROP4'`,
   "!p q c. DET c ==> !s. WLP(c,p)s \/ WLP(c,q)s = WLP(c, \s. p s \/ q s)s",
   REWRITE_TAC[DET]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[WLP_PROP4;WLP_THM]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[DISJ_IMP_LEMMA]
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[NOT_IMP_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. REWRITE_TAC[el 3 thl])
    THENL[ASM_REWRITE_TAC[];RES_TAC]);;


% Now we prove properties about particular command types %

let SKIP_WP =
 prove_thm
  (`SKIP_WP`,
   "!p. WP(MK_SKIP,p) = p",
   REWRITE_TAC[WP_THM;MK_SKIP]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o mapfilter SYM)
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "f:state"
    THEN REWRITE_TAC[]);;

let SKIP_WLP =
 prove_thm
  (`SKIP_WLP`,
   "!p. WLP(MK_SKIP,p) = p",
   REWRITE_TAC[WLP_THM;MK_SKIP]
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[ASSUME_TAC(REFL "f:state"); ALL_TAC]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o mapfilter SYM)
    THEN ASM_REWRITE_TAC[]);;

let ABORT_WP =
 prove_thm
  (`ABORT_WP`,
   "!p. WP(MK_ABORT,p) = \s.F",
   REWRITE_TAC[WP_THM;MK_ABORT]
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC);;

let ABORT_WLP =
 prove_thm
  (`ABORT_WLP`,
   "!p. WLP(MK_ABORT,p) = \s.T",
   REWRITE_TAC[WLP_THM;MK_ABORT]
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC);;

let ASSIGN_WP =
 prove_thm
  (`ASSIGN_WP`,
   "!x f p. WP(MK_ASSIGN(x,f),p) = \s. p (BND (f s) x s)",
   REWRITE_TAC[WP_THM;MK_ASSIGN]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM(\th.EXISTS_TAC(rand(concl th)))
    THEN REWRITE_TAC[]);;

let ASSIGN_WLP =
 prove_thm
  (`ASSIGN_WLP`,
   "!x f p. WLP(MK_ASSIGN(x,f),p) = \s. p (BND (f s) x s)",
   REWRITE_TAC[WLP_THM;MK_ASSIGN]
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. REWRITE_TAC(mapfilter SYM thl))
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM
          (\th. (REWRITE_TAC[REWRITE_RULE[](SPEC t th)]
                 where
                 t = rhs(fst(dest_imp(snd(dest_forall(concl th))))))));;

let SEQ_WP =
 prove_thm
  (`SEQ_WP`,
   "!c1 c2 p.  DET c1 ==> !s. (WP(MK_SEQ(c1,c2),p)s = WP(c1,WP(c2,p))s)",
   REWRITE_TAC[WP_THM;MK_SEQ;DET] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT (EQ_TAC ORELSE STRIP_TAC) THENL
   [EXISTS_TAC "s'':state" THEN FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC "s':state" THEN RES_TAC THEN
    SUBST1_TAC (ASSUME "s''':state = s''") THEN
    FIRST_ASSUM ACCEPT_TAC;
    RES_TAC;
    RES_TAC THEN
    MAP_EVERY EXISTS_TAC ["s'':state";"s':state"] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    RES_TAC]);;

% The material below shows that without the assumption that
  DET c1 it is not the case that
  WP(MK_SEQ(c1,c2),p)s = WP(c1,WP(c2,p))s

let S1 = new_definition(`S1`, "(S1:state) str = 0");;
let S2 = new_definition(`S2`, "(S2:state) str = 1");;

let S1_NOT_S2 =
 prove_thm
  (`S1_NOT_S2`,
   "~(S1 = S2)",
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV)
   THEN CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV)
   THEN REWRITE_TAC[S1;S2;num_CONV "1";NOT_EQ_SYM(SPEC_ALL NOT_SUC)]);;

let C1 =
 new_definition
  (`C1`,
   "C1(s1,s2) =  (s2 = S1) \/ (s2 = S2)");;

let C2 =
 new_definition
  (`C2`,
   "C2(s1,s2) = (s1 = S1) /\ (s2 = S1)");;

let C1_C2 =
 prove_thm
  (`C1_C2`,
   "MK_SEQ(C1,C2)(s1,s2) = (s2 = S1)",
   REWRITE_TAC[MK_SEQ;C1;C2]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC "S1"
    THEN ASM_REWRITE_TAC[]);;

let WP_C1_C2 =
 prove_thm
  (`WP_C1_C2`,
   "WP(MK_SEQ(C1,C2),p)s = p S1",
   REWRITE_TAC[WP_THM;MK_SEQ;C1;C2]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN (POP_ASSUM(MAP_EVERY(ASSUME_TAC o GEN_ALL) o IMP_CANON)
          ORELSE ALL_TAC)
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "S1"
    THEN EXISTS_TAC "S1"
    THEN REWRITE_TAC[]);;

let WP_C2 =
 prove_thm
  (`WP_C2`,
   "WP(C2,p)s = (s=S1) /\ p S1",
   REWRITE_TAC[WP_THM;C2]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "S1"
    THEN REWRITE_TAC[]);;

let WP_C1_WP_C2 =
 prove_thm
  (`WP_C1_WP_C2`,
   "WP(C1,WP(C2,p))s = F",
   REWRITE_TAC[WP_C2;WP_THM;C1;C2]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EQ_SYM S1_NOT_S2] o SPEC "S2")
    THEN ASM_REWRITE_TAC[]);;

let NOT_SEQ_WP =
 prove_thm
  (`NOT_SEQ_WP`,
   "~!c1 c2 p s. (WP(MK_SEQ(c1,c2),p)s = WP(c1,WP(c2,p))s)",
   CONV_TAC(TOP_DEPTH_CONV NOT_FORALL_CONV)
    THEN EXISTS_TAC "C1"
    THEN EXISTS_TAC "C2"
    THEN REWRITE_TAC[WP_C1_C2;WP_C1_WP_C2]
    THEN EXISTS_TAC "\p:state.T"
    THEN BETA_TAC);;
%

% Determinacy is not needed with weakest liberal preconditions %

let SEQ_WLP =
 prove_thm
  (`SEQ_WLP`,
   "!c1 c2 p s. (WLP(MK_SEQ(c1,c2),p)s = WLP(c1,WLP(c2,p))s)",
   REWRITE_TAC[WLP_THM;MK_SEQ]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(ASSUME_TAC o GEN_ALL o hd o IMP_CANON o (el 3))
    THEN POP_ASSUM(ASSUME_TAC o SPECL["s':state";"s'':state"])
    THEN RES_TAC);;

let IF1_WP =
 prove_thm
  (`IF1_WP`,
   "!c b p s. WP(MK_IF1(b,c),p)s = (b s => WP(c,p)s | p s)",
   REWRITE_TAC[WP_THM;MK_IF1]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [EXISTS_TAC "s:state";
      POP_ASSUM(\th. REWRITE_TAC[SYM th])]
    THEN ASM_REWRITE_TAC[]);;

let IF1_WLP =
 prove_thm
  (`IF1_WLP`,
   "!c b p s. WLP(MK_IF1(b,c),p)s = (b s => WLP(c,p)s | p s)",
   REWRITE_TAC[WLP_THM;MK_IF1]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [ASSUME_TAC(REFL "s:state")
       THEN RES_TAC;
      POP_ASSUM(\th. REWRITE_TAC[SYM th])]
    THEN ASM_REWRITE_TAC[]);;

let IF2_WP =
 prove_thm
  (`IF2_WP`,
   "!c1 c2 p s. WP(MK_IF2(b,c1,c2),p)s = (b s => WP(c1,p)s | WP(c2,p)s)",
   REWRITE_TAC[WP_THM;MK_IF2]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC);;

let IF2_WLP =
 prove_thm
  (`IF2_WLP`,
   "!c1 c2 p s. WLP(MK_IF2(b,c1,c2),p)s = (b s => WLP(c1,p)s | WLP(c2,p)s)",
   REWRITE_TAC[WLP_THM;MK_IF2]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT STRIP_TAC);;


% ITER : num -> (state->bool) # command -> command

     ITER 0 (b,c) (s,s')        =  ~(b s) /\ (s = s')

     ITER (SUC n) (b,c) (s,s')  =   b s /\ MK_SEQ(c, ITER n (b,c))(s,s')
%

let ITER =
 new_prim_rec_definition
  (`ITER`,
   "(ITER 0       = \(b,c) (s,s'). ~(b s) /\ (s = s')) /\
    (ITER (SUC n) = \(b,c) (s,s'). b s /\ MK_SEQ(c, ITER n (b,c))(s,s'))");;

load_definition `bool` `UNCURRY_DEF`;;

let ITER_CLAUSES =
 prove_thm
  (`ITER_CLAUSES`,
   "(ITER 0       (b,c) (s,s')  =  ~(b s) /\ (s = s')) /\
    (ITER (SUC n) (b,c) (s,s')  =
      b s /\ MK_SEQ(c, ITER n (b,c))(s,s'))",
   PURE_REWRITE_TAC[ITER]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[]);;

let COND_LEMMA =
 TAUT_PROVE
 "!b t1 t2. (b => t1 | t2) = (b ==> t1) /\ (~b ==> t2)";;

load_theorem `hoare_thms` `MK_FINITE_WHILE_CLAUSES`;;

let WHILE_ITER1 =
 prove_thm
  (`WHILE_ITER1`,
   "MK_WHILE(b,c)(s,s') ==> ?n. ITER n (b,c) (s,s')",
   REWRITE_TAC[MK_WHILE]
    THEN STRIP_TAC
    THEN ASSUM_LIST(\[th]. UNDISCH_TAC(concl th))
    THEN SPEC_TAC("s':state","s':state")
    THEN SPEC_TAC("s:state","s:state")
    THEN SPEC_TAC("n:num","n:num")
    THEN INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;MK_IF1;MK_SEQ;COND_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THENL
     [POP_ASSUM STRIP_ASSUME_TAC
       THEN RES_TAC
       THEN POP_ASSUM STRIP_ASSUME_TAC
       THEN EXISTS_TAC "SUC n'"                  % changed n'' -> n' TFM %
       THEN ASM_REWRITE_TAC[ITER_CLAUSES;MK_SEQ]
       THEN EXISTS_TAC "s'':state"
       THEN ASM_REWRITE_TAC[];
      EXISTS_TAC "0"
       THEN ASM_REWRITE_TAC[ITER_CLAUSES;MK_SEQ]]);;

let WHILE_ITER2 =
 prove_thm
  (`WHILE_ITER2`,
   "!n s s'. ITER n (b,c) (s,s') ==> MK_WHILE(b,c)(s,s')",
   REWRITE_TAC[MK_WHILE]
    THEN INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES;MK_SEQ]
    THEN REPEAT STRIP_TAC
    THENL
     [EXISTS_TAC "SUC 0"
       THEN ASM_REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;MK_IF1;MK_SEQ];
      RES_TAC
       THEN POP_ASSUM STRIP_ASSUME_TAC
       THEN EXISTS_TAC "SUC n'"
       THEN ASM_REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;MK_IF1;MK_SEQ]
       THEN EXISTS_TAC "s'':state"
       THEN ASM_REWRITE_TAC[]]);;

let WHILE_ITER =
 prove_thm
  (`WHILE_ITER`,
   "MK_WHILE(b,c)(s,s') = ?n. ITER n (b,c) (s,s')",
   EQ_TAC
    THENL
     [ACCEPT_TAC WHILE_ITER1;
      REPEAT STRIP_TAC
       THEN IMP_RES_TAC WHILE_ITER2]);;

% Commented-out because last is now defined     %
% in the basic HOL system [RJB 90.10.20].       %
%                                               %
% letrec last l = last(tl l) ? hd l;;           %

let ITER_UNIQUE =
 prove_thm
  (`ITER_UNIQUE`,
   "DET c ==>
     !n s s'. ITER n(b,c)(s,s') ==>
               !n' s''. ITER n'(b,c)(s,s'') ==> (n = n')",
   DISCH_TAC THEN INDUCT_TAC THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC[ITER_CLAUSES;MK_SEQ] THEN
   STRIP_TAC THENL
    [INDUCT_TAC THEN GEN_TAC THENL
      [REWRITE_TAC[ITER_CLAUSES];ASM_REWRITE_TAC[ITER_CLAUSES]];
     INDUCT_TAC THEN GEN_TAC THEN
     ASM_REWRITE_TAC[ITER_CLAUSES;MK_SEQ;INV_SUC_EQ] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN IMP_RES_TAC DET THEN
     ASSUM_LIST(\thl. ASSUME_TAC(SUBS[el 3 thl](el 5 thl))) THEN
     RES_TAC]);;

let ITER_WP =
 new_prim_rec_definition
  (`ITER_WP`,
   "(ITER_WP 0       b c p s = ~(b s) /\ p s) /\
    (ITER_WP (SUC n) b c p s = b s /\ WP(c,ITER_WP n b c p) s)");;

let DET_ITER =
 prove_thm
  (`DET_ITER`,
   "DET c ==> !n. DET(ITER n (b,c))",
   REWRITE_TAC[DET]
    THEN DISCH_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[ITER_CLAUSES;MK_SEQ]
    THEN REPEAT STRIP_TAC
    THENL
     [ASSUM_LIST(REWRITE_TAC o (mapfilter SYM));
      RES_TAC THEN
      SUBST_ALL_TAC (ASSUME "s''':state = s''") THEN
      RES_TAC]);;

let WP_ITER =
 prove_thm
  (`WP_ITER`,
   "DET c ==> !n. !s. WP(ITER n (b,c),p) s =  ITER_WP n b c p s",
   DISCH_TAC
    THEN INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES;ITER_WP;WP_THM]
    THEN BETA_TAC
    THENL
     [EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
       THEN ASM_REWRITE_TAC[]
       THEN EXISTS_TAC "s:state"
       THEN REWRITE_TAC[];
      ALL_TAC]
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter(SYM o SPEC_ALL)))
    THEN REWRITE_TAC[WP_THM;MK_SEQ]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC []
    THENL
     [EXISTS_TAC "s'':state" THEN FIRST_ASSUM ACCEPT_TAC;
      IMP_RES_THEN IMP_RES_TAC DET THEN
      EXISTS_TAC "s':state" THEN
      SUBST1_TAC (ASSUME "s''':state = s''") THEN
      FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC "s'':state" THEN
      EXISTS_TAC "s':state" THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let WHILE_WP =
 prove_thm
  (`WHILE_WP`,
   "!c. DET c ==> !b p s. WP(MK_WHILE(b,c),p)s = ?n. ITER_WP n b c p s",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[WHILE_ITER;WP_THM]
    THEN BETA_TAC
    THEN REWRITE_TAC [SYM(SPEC_ALL(UNDISCH WP_ITER))]
    THEN REWRITE_TAC[WP_THM]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [EXISTS_TAC "n:num" THEN CONJ_TAC THENL
      [EXISTS_TAC "s':state" THEN FIRST_ASSUM ACCEPT_TAC;
       REPEAT STRIP_TAC THEN RES_TAC];
      EXISTS_TAC "s':state"
      THEN EXISTS_TAC "n:num"
      THEN ASM_REWRITE_TAC[];
      IMP_RES_TAC DET_ITER
       THEN ASSUM_LIST(IMP_RES_TAC o REWRITE_RULE[DET] o hd)
       THEN IMP_RES_TAC ITER_UNIQUE
       THEN FIRST_ASSUM MATCH_MP_TAC
       THEN SUBST1_TAC (ASSUME "n:num = n'")
       THEN FIRST_ASSUM ACCEPT_TAC]);;

% Some unused lemmas

let FINITE_WHILE_WP_0 =
 prove_thm
  (`FINITE_WHILE_WP_0`,
   "WP(MK_FINITE_WHILE 0 (b,c),p)s =  F",
   REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;ITER_WP;WP_THM]);;

let LEMMA1 =
 TAC_PROOF
  (([], "(?s'. s = s') /\ (!s'. (s = s') ==> p s') = p s"),
   EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
    THEN ASM_REWRITE_TAC[]
    THEN EXISTS_TAC "s:state"
    THEN ASM_REWRITE_TAC[]);;

let FINITE_WHILE_WP_SUC =
 prove_thm
  (`FINITE_WHILE_WP_SUC`,
   "WP(MK_FINITE_WHILE (SUC n) (b,c),p)s =
    (b s => WP(MK_SEQ(c,MK_FINITE_WHILE n(b,c)),p) s | p s)",
   REWRITE_TAC[MK_FINITE_WHILE_CLAUSES;ITER_WP;WP_THM]
    THEN BETA_TAC
    THEN REWRITE_TAC[MK_FINITE_WHILE_CLAUSES]
    THEN ASM_CASES_TAC "(b:state->bool)s"
    THEN ASM_REWRITE_TAC[MK_SEQ;MK_IF1;LEMMA1]);;
%


let ITER_WLP =
 new_prim_rec_definition
  (`ITER_WLP`,
   "(ITER_WLP 0       b c p s = ~(b s) ==> p s) /\
    (ITER_WLP (SUC n) b c p s = b s ==> WLP(c,ITER_WLP n b c p) s)");;

let WLP_ITER =
 prove_thm
  (`WLP_ITER`,
   "!n. !s. WLP(ITER n (b,c),p) s =  ITER_WLP n b c p s",
   INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[ITER_CLAUSES;ITER_WLP;WLP_THM]
    THEN BETA_TAC
    THENL
     [EQ_TAC
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN ASSUM_LIST(REWRITE_TAC o (mapfilter SYM))
       THEN ASM_REWRITE_TAC[]
       THEN ASSUM_LIST
             (\[th1;th2;th3]. ASSUME_TAC(REWRITE_RULE[](SPEC "s:state" th3)))
       THEN RES_TAC;
      ALL_TAC]
    THEN ASSUM_LIST(REWRITE_TAC o (mapfilter(SYM o SPEC_ALL)))
    THEN REWRITE_TAC[WLP_THM;MK_SEQ]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. ASSUME_TAC(SPEC "s'':state" (el 5 thl)))
    THEN POP_ASSUM(\th. ASSUME_TAC(GEN "s''':state" (hd(IMP_CANON th))))
    THEN RES_TAC);;


let WHILE_WLP =
 prove_thm
  (`WHILE_WLP`,
   "!c b p s. WLP(MK_WHILE(b,c),p)s = !n. ITER_WLP n b c p s",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[WHILE_ITER;WLP_THM;SYM(SPEC_ALL WLP_ITER)]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. ASSUME_TAC(GEN_ALL(hd( IMP_CANON(el 2 thl)))))
    THEN RES_TAC);;

close_theory();;
