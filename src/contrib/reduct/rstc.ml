%============================================================================%
%        FILE: rstc.ml                                                       %
%                                                                            %
% DESCRIPTION: Collection of theorems about (all combinations of) reflexive, %
%              symmetric and transitive closure of binary relations.         %
%                                                                            %
%      AUTHOR: John Harrison                                                 %
%              University of Cambridge Computer Laboratory                   %
%              New Museums Site                                              %
%              Pembroke Street                                               %
%              Cambridge CB2 3QG                                             %
%              England.                                                      %
%                                                                            %
%        DATE: 27th May 1993                                                 %
%============================================================================%

timer true;;

can unlink `RSTC.th`;;

new_theory `RSTC`;;

load_library `ind_defs`;;

map hide_constant [`I`; `K`; `S`];;

%----------------------------------------------------------------------------%
% Useful oddments                                                            %
%----------------------------------------------------------------------------%

let LAND_CONV = RATOR_CONV o RAND_CONV;;

let TAUT_CONV =
  let val w t = type_of t = ":bool" & can (find_term is_var) t & free_in t w in
  C (curry prove)
  (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
   (C $THEN (REWRITE_TAC[]) o BOOL_CASES_TAC o hd o sort (uncurry free_in) o
    W(find_terms o val) o snd));;

let ANTE_RES_THEN ttac th = FIRST_ASSUM(ttac o C MATCH_MP th);;

let RULE_INDUCT_TAC = C W STRIP_ASSUME_TAC o RULE_INDUCT_THEN;;

%----------------------------------------------------------------------------%
% Little lemmas about equivalent forms of symmetry and transitivity.         %
%----------------------------------------------------------------------------%

let SYM_ALT = prove_thm(`SYM_ALT`,
  "!R:*->*->bool. (!x y. R x y ==> R y x) = (!x y. R x y = R y x)",
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC;
    FIRST_ASSUM(\th. GEN_REWRITE_TAC I [] [th])] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let TRANS_ALT = prove_thm(`TRANS_ALT`,
  "!(R:*->*->bool) (S:*->*->bool) U.
        (!x z. (?y. R x y /\ S y z) ==> U x z) =
        (!x y z. R x y /\ S y z ==> U x z)",
  REPEAT GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV LEFT_IMP_EXISTS_CONV) THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Reflexive closure                                                          %
%----------------------------------------------------------------------------%

let RC_CLAUSES,RC_INDUCT =
  let RC = "RC:(*->*->bool)->(*->*->bool)"
  and R = "R:*->*->bool" in
  new_inductive_definition false `RC`
  ("^RC ^R x y",["^R"])
  [                  ["^R x y"],"^RC ^R x y";
                             [],"^RC ^R x x"];;

let RC_INC = prove_thm(`RC_INC`,
  "!(R:*->*->bool) x y. R x y ==> RC R x y",
  REWRITE_TAC RC_CLAUSES);;

let RC_REFL = prove_thm(`RC_REFL`,
  "!(R:*->*->bool) x. RC R x x",
  REWRITE_TAC RC_CLAUSES);;

let RC_CASES = prove_thm(`RC_CASES`,
  "!(R:*->*->bool) x y. RC R x y = R x y \/ (x = y)",
  GEN_TAC THEN REWRITE_TAC[derive_cases_thm (RC_CLAUSES,RC_INDUCT)] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
  ASM_REWRITE_TAC[]);;

let RC_INDUCT = prove_thm(`RC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) ==>
            (!x y. RC R x y ==> P x y)",
  MATCH_ACCEPT_TAC RC_INDUCT);;

let RC_MONO = prove_thm(`RC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
            (!x y. RC R x y ==> RC S x y)",
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let RC_CLOSED = prove_thm(`RC_CLOSED`,
  "!R:*->*->bool. (RC R = R) = !x. R x x",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC RC_REFL;
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[RC_CASES] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let RC_IDEMP = prove_thm(`RC_IDEMP`,
  "!R:*->*->bool. RC(RC R) = RC R",
  REWRITE_TAC[RC_CLOSED; RC_REFL]);;

let RC_SYM = prove_thm(`RC_SYM`,
  "!R:*->*->bool.
        (!x y. R x y ==> R y x) ==> (!x y. RC R x y ==> RC R y x)",
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RC_TRANS = prove_thm(`RC_TRANS`,
  "!R:*->*->bool.
        (!x z. (?y. R x y /\ R y z) ==> R x z) ==>
        (!x z. (?y. RC R x y /\ RC R y z) ==> RC R x z)",
  REWRITE_TAC[RC_CASES] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM(UNDISCH_TAC o assert is_eq o concl) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]]);;

%----------------------------------------------------------------------------%
% Symmetric closure                                                          %
%----------------------------------------------------------------------------%

let SC_CLAUSES,SC_INDUCT =
  let SC = "SC:(*->*->bool)->(*->*->bool)"
  and R = "R:*->*->bool" in
  new_inductive_definition false `SC`
  ("^SC ^R x y",["^R"])
  [                  ["^R x y"],"^SC ^R x y";
                 ["^SC ^R x y"],"^SC ^R y x"];;

let SC_INC = prove_thm(`SC_INC`,
  "!(R:*->*->bool) x y. R x y ==> SC R x y",
  REWRITE_TAC SC_CLAUSES);;

let SC_SYM = prove_thm(`SC_SYM`,
  "!(R:*->*->bool) x y. SC R x y ==> SC R y x",
  REWRITE_TAC SC_CLAUSES);;

let SC_CASES = prove_thm(`SC_CASES`,
  "!R:*->*->bool. SC(R) x y = R x y \/ R y x",
  GEN_TAC THEN EQ_TAC THENL
   [RULE_INDUCT_TAC SC_INDUCT THEN
    ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_REWRITE_TAC[];
    DISCH_THEN DISJ_CASES_TAC THENL
     [ALL_TAC; MATCH_MP_TAC SC_SYM] THEN
    MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]]);;

let SC_INDUCT = prove_thm(`SC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) ==>
            (!x y. SC R x y ==> P x y)",
  MATCH_ACCEPT_TAC SC_INDUCT);;

let SC_MONO = prove_thm(`SC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. SC R x y ==> SC S x y)",
  REWRITE_TAC[SC_CASES] THEN REPEAT STRIP_TAC THEN
  RES_TAC THEN ASM_REWRITE_TAC[]);;

let SC_CLOSED = prove_thm(`SC_CLOSED`,
  "!R:*->*->bool. (SC R = R) = !x y. R x y ==> R y x",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SC_SYM;
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[SC_CASES] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let SC_IDEMP = prove_thm(`SC_IDEMP`,
  "!R:*->*->bool. SC(SC R) = SC R",
  REWRITE_TAC[SC_CLOSED; SC_SYM]);;

let SC_REFL = prove_thm(`SC_REFL`,
  "!R:*->*->bool. (!x. R x x) ==> (!x. SC R x x)",
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SC_CASES] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Transitive closure                                                         %
%----------------------------------------------------------------------------%

let TC_CLAUSES,TC_INDUCT =
  let TC = "TC:(*->*->bool)->(*->*->bool)"
  and R = "R:*->*->bool" in
  new_inductive_definition false `TC`
  ("^TC ^R x y",["^R"])
  [                  ["^R x y"],"^TC ^R x y";
   ["^TC ^R x y"; "^TC ^R y z"],"^TC ^R x z"];;

let TC_INC = prove_thm(`TC_INC`,
  "!(R:*->*->bool) x y. R x y ==> TC R x y",
  REWRITE_TAC TC_CLAUSES);;

let TC_TRANS = prove_thm(`TC_TRANS`,
  "!(R:*->*->bool) x z. (?y. TC R x y /\ TC R y z) ==> TC R x z",
  REWRITE_TAC TC_CLAUSES);;

let TC_CASES = prove_thm(`TC_CASES`,
  "!(R:*->*->bool) x z. TC R x z = R x z \/ (?y. TC R x y /\ TC R y z)",
  MATCH_ACCEPT_TAC (derive_cases_thm (TC_CLAUSES,TC_INDUCT)));;

let TC_INDUCT = prove_thm(`TC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)",
  MATCH_ACCEPT_TAC TC_INDUCT);;

let TC_MONO = prove_thm(`TC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. TC R x y ==> TC S x y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC;
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*"] THEN
  ASM_REWRITE_TAC[]);;

let TC_CLOSED = prove_thm(`TC_CLOSED`,
  "!R:*->*->bool. (TC R = R) = !x z. (?y. R x y /\ R y z) ==> R x z",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC TC_TRANS;
    DISCH_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN EQ_TAC THENL
     [RULE_INDUCT_TAC TC_INDUCT THEN FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC TC_INC]]);;

let TC_IDEMP = prove_thm(`TC_IDEMP`,
  "!R:*->*->bool. TC(TC R) = TC R",
  REWRITE_TAC[TC_CLOSED; TC_TRANS]);;

let TC_REFL = prove_thm(`TC_REFL`,
  "!R:*->*->bool. (!x. R x x) ==> (!x. TC R x x)",
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[]);;

let TC_SYM = prove_thm(`TC_SYM`,
  "!R:*->*->bool. (!x y. R x y ==> R y x) ==> (!x y. TC R x y ==> TC R y x)",
  GEN_TAC THEN DISCH_TAC THEN RULE_INDUCT_TAC TC_INDUCT THENL
   [MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_MP_TAC;
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*" THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Commutativity properties of the three basic closure operations             %
%----------------------------------------------------------------------------%

let RC_SC = prove_thm(`RC_SC`,
  "!R:*->*->bool. RC(SC R) = SC(RC R)",
  GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "x:*" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
  REWRITE_TAC[RC_CASES; SC_CASES] THEN
  SUBST1_TAC(ISPECL ["x:*"; "y:*"] EQ_SYM_EQ) THEN
  ASM_CASES_TAC "y:* = x" THEN ASM_REWRITE_TAC[]);;

let SC_RC = prove_thm(`SC_RC`,
  "!R:*->*->bool. SC(RC R) = RC(SC R)",
  MATCH_ACCEPT_TAC(GSYM RC_SC));;

let RC_TC = prove_thm(`RC_TC`,
  "!R:*->*->bool. RC(TC R) = TC(RC R)",
  GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "x:*" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN EQ_TAC THENL
   [RULE_INDUCT_TAC RC_INDUCT THENL
     [POP_ASSUM MP_TAC THEN MATCH_MP_TAC TC_MONO THEN
      MATCH_ACCEPT_TAC RC_INC;
      MATCH_MP_TAC TC_REFL THEN MATCH_ACCEPT_TAC RC_REFL];
    RULE_INDUCT_TAC TC_INDUCT THENL
     [POP_ASSUM MP_TAC THEN MATCH_MP_TAC RC_MONO THEN
      MATCH_ACCEPT_TAC TC_INC;
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
      MATCH_MP_TAC(REWRITE_RULE[TRANS_ALT] RC_TRANS) THEN
      MATCH_ACCEPT_TAC(REWRITE_RULE[TRANS_ALT] TC_TRANS)]]);;

let TC_RC = prove_thm(`TC_RC`,
  "!R:*->*->bool. TC(RC R) = RC(TC R)",
  MATCH_ACCEPT_TAC(GSYM RC_TC));;

let TC_SC = prove_thm(`TC_SC`,
  "!(R:*->*->bool) x y. SC(TC R) x y ==> TC(SC R) x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[SC_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC SC_INC;
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC TC_INC THEN ASM_REWRITE_TAC[SC_CASES];
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*" THEN
      ASM_REWRITE_TAC[]]]);;

let SC_TC = prove_thm(`SC_TC`,
  "!(R:*->*->bool) x y. SC(TC R) x y ==> TC(SC R) x y",
  MATCH_ACCEPT_TAC TC_SC);;

%----------------------------------------------------------------------------%
% Useful to have "left" and "right" recursive versions of transitivity       %
%----------------------------------------------------------------------------%

let TCL_CLAUSES,TCL_INDUCT =
  let TC = "TCL:(*->*->bool)->(*->*->bool)"
  and R = "R:*->*->bool" in
  new_inductive_definition false `TCL`
  ("^TC ^R x y",["^R"])
  [                  ["^R x y"],"^TC ^R x y";
   ["^TC ^R x y"; "^R y z"],"^TC ^R x z"];;

let TCR_CLAUSES,TCR_INDUCT =
  let TC = "TCR:(*->*->bool)->(*->*->bool)"
  and R = "R:*->*->bool" in
  new_inductive_definition false `TC2`
  ("^TC ^R x y",["^R"])
  [                  ["^R x y"],"^TC ^R x y";
   ["^R x y"; "^TC ^R y z"],"^TC ^R x z"];;

%----------------------------------------------------------------------------%
% Prove them both equivalent to TC.                                          %
%----------------------------------------------------------------------------%

let TCL_TRANS = prove_thm(`TCL_TRANS`,
  "!(R:*->*->bool) x y z. TCL R x y /\ TCL R y z ==> TCL R x z",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV "a /\ b ==> c = b ==> a ==> c"] THEN
  DISCH_TAC THEN SPEC_TAC("x:*","x:*") THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC("z:*","z:*") THEN
  SPEC_TAC("y:*","y:*") THEN RULE_INDUCT_TAC TCL_INDUCT THENL
   [X_GEN_TAC "z:*" THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCL_CLAUSES) THEN
    EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCL_CLAUSES) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let TCL_TC = prove_thm(`TCL_TC`,
  "TCL:(*->*->bool)->(*->*->bool) = TC",
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "R:*->*->bool" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "x:*" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
  EQ_TAC THENL
   [RULE_INDUCT_TAC TCL_INDUCT THENL
     [MATCH_MP_TAC TC_INC;
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*"] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TC_INC;
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC (el 1 TCL_CLAUSES);
      MATCH_MP_TAC TCL_TRANS THEN EXISTS_TAC "y:*"]] THEN
  ASM_REWRITE_TAC[]);;

let TCR_TRANS = prove_thm(`TCR_TRANS`,
  "!(R:*->*->bool) x y z. TCR R x y /\ TCR R y z ==> TCR R x z",
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV "a /\ b ==> c = a ==> b ==> c"] THEN
  DISCH_TAC THEN SPEC_TAC("z:*","z:*") THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC("y:*","y:*") THEN
  SPEC_TAC("x:*","x:*") THEN RULE_INDUCT_TAC TCR_INDUCT THENL
   [X_GEN_TAC "z:*" THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCR_CLAUSES) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[];
    X_GEN_TAC "w:*" THEN DISCH_TAC THEN
    MATCH_MP_TAC (el 2 TCR_CLAUSES) THEN
    EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let TCR_TC = prove_thm(`TCR_TC`,
  "TCR:(*->*->bool)->(*->*->bool) = TC",
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "R:*->*->bool" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "x:*" THEN
  CONV_TAC FUN_EQ_CONV THEN X_GEN_TAC "y:*" THEN
  EQ_TAC THENL
   [RULE_INDUCT_TAC TCR_INDUCT THENL
     [MATCH_MP_TAC TC_INC;
      MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*"] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TC_INC;
    RULE_INDUCT_TAC TC_INDUCT THENL
     [MATCH_MP_TAC (el 1 TCR_CLAUSES);
      MATCH_MP_TAC TCR_TRANS THEN EXISTS_TAC "y:*"]] THEN
  ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Really we just want these theorems, then we can forget TCL and TCR         %
%----------------------------------------------------------------------------%

let TC_TRANS_L = prove_thm(`TC_TRANS_L`,
  "!(R:*->*->bool) x z. (?y. TC R x y /\ R y z) ==> TC R x z",
  REWRITE_TAC[GSYM TCL_TC] THEN REWRITE_TAC TCL_CLAUSES);;

let TC_TRANS_R = prove_thm(`TC_TRANS_R`,
  "!(R:*->*->bool) x z. (?y. R x y /\ TC R y z) ==> TC R x z",
  REWRITE_TAC[GSYM TCR_TC] THEN REWRITE_TAC TCR_CLAUSES);;

let TC_INDUCT_L = prove_thm(`TC_INDUCT_L`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. P x y /\ R y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)",
  REWRITE_TAC[GSYM TCL_TC] THEN MATCH_ACCEPT_TAC TCL_INDUCT);;

let TC_INDUCT_R = prove_thm(`TC_INDUCT_R`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
            (!x y. TC R x y ==> P x y)",
  REWRITE_TAC[GSYM TCR_TC] THEN MATCH_ACCEPT_TAC TCR_INDUCT);;

let TC_CASES_L = prove_thm(`TC_CASES_L`,
  "!(R:*->*->bool) x z. TC R x z = R x z \/ (?y. TC R x y /\ R y z)",
  REWRITE_TAC[GSYM TCL_TC] THEN
  MATCH_ACCEPT_TAC (derive_cases_thm (TCL_CLAUSES,TCL_INDUCT)));;

let TC_CASES_R = prove_thm(`TC_CASES_R`,
  "!(R:*->*->bool) x z. TC R x z = R x z \/ (?y. R x y /\ TC R y z)",
  REWRITE_TAC[GSYM TCR_TC] THEN
  MATCH_ACCEPT_TAC (derive_cases_thm (TCR_CLAUSES,TCR_INDUCT)));;

%----------------------------------------------------------------------------%
% Reflexive symmetric closure                                                %
%----------------------------------------------------------------------------%

let RSC = new_definition(`RSC`,
  "!R:*->*->bool. RSC(R) = RC(SC R)");;

let RSC_INC = prove_thm(`RSC_INC`,
  "!(R:*->*->bool) x y. R x y ==> RSC R x y",
  REPEAT STRIP_TAC THEN REWRITE_TAC[RSC] THEN
  MATCH_MP_TAC RC_INC THEN MATCH_MP_TAC SC_INC THEN
  ASM_REWRITE_TAC[]);;

let RSC_REFL = prove_thm(`RSC_REFL`,
  "!(R:*->*->bool) x. RSC R x x",
  REWRITE_TAC[RSC; RC_REFL]);;

let RSC_SYM = prove_thm(`RSC_SYM`,
  "!(R:*->*->bool) x y. RSC R x y ==> RSC R y x",
  REWRITE_TAC[RSC; RC_SC; SC_SYM]);;

let RSC_CASES = prove_thm(`RSC_CASES`,
  "!(R:*->*->bool) x y. RSC R x y = (x = y) \/ R x y \/ R y x",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC; RC_CASES; SC_CASES] THEN
  CONV_TAC(AC_CONV(DISJ_ASSOC,DISJ_SYM)));;

let RSC_INDUCT = prove_thm(`RSC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) ==>
                !x y. RSC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RSC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "SC(R:*->*->bool) x y" THEN
  RULE_INDUCT_TAC SC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(\th. MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

let RSC_MONO = prove_thm(`RSC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSC R x y ==> RSC S x y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RSC] THEN
  MATCH_MP_TAC RC_MONO THEN MATCH_MP_TAC SC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let RSC_CLOSED = prove_thm(`RSC_CLOSED`,
  "!R:*->*->bool. (RSC R = R) = (!x. R x x) /\ (!x y. R x y ==> R y x)",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RSC_REFL; RSC_SYM];
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    REWRITE_TAC[RSC_CASES] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let RSC_IDEMP = prove_thm(`RSC_IDEMP`,
  "!R:*->*->bool. RSC(RSC R) = RSC R",
  REWRITE_TAC[RSC_CLOSED; RSC_REFL; RSC_SYM]);;

%----------------------------------------------------------------------------%
% Reflexive transitive closure                                               %
%----------------------------------------------------------------------------%

let RTC = new_definition(`RTC`,
  "!R:*->*->bool. RTC(R) = RC(TC R)");;

let RTC_INC = prove_thm(`RTC_INC`,
  "!(R:*->*->bool) x y. R x y ==> RTC R x y",
  REPEAT STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_INC THEN MATCH_MP_TAC TC_INC THEN
  ASM_REWRITE_TAC[]);;

let RTC_REFL = prove_thm(`RTC_REFL`,
  "!(R:*->*->bool) x. RTC R x x",
  REWRITE_TAC[RTC; RC_REFL]);;

let RTC_TRANS = prove_thm(`RTC_TRANS`,
  "!(R:*->*->bool) x z. (?y. RTC R x y /\ RTC R y z) ==> RTC R x z",
  REWRITE_TAC[RTC; RC_TC; TC_TRANS]);;

let RTC_TRANS_L = prove_thm(`RTC_TRANS_L`,
  "!(R:*->*->bool) x z. (?y. RTC R x y /\ R y z) ==> RTC R x z",
  REWRITE_TAC[RTC; RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC "y:*" THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RC_INC THEN
  ASM_REWRITE_TAC[]);;

let RTC_TRANS_R = prove_thm(`RTC_TRANS_R`,
  "!(R:*->*->bool) x z. (?y. R x y /\ RTC R y z) ==> RTC R x z",
  REWRITE_TAC[RTC; RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC "y:*" THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RC_INC THEN
  ASM_REWRITE_TAC[]);;

let RTC_CASES = prove_thm(`RTC_CASES`,
  "!(R:*->*->bool) x z. RTC R x z = (x = z) \/ ?y. RTC R x y /\ RTC R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC; RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN EXISTS_TAC "x:*";
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*";
    DISJ1_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[]);;

let RTC_CASES_L = prove_thm(`RTC_CASES_L`,
  "!(R:*->*->bool) x z. RTC R x z = (x = z) \/ ?y. RTC R x y /\ R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC; RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_L]) THENL
     [DISJ2_TAC THEN EXISTS_TAC "x:*";
      FIRST_ASSUM(X_CHOOSE_TAC "y:*") THEN DISJ2_TAC THEN EXISTS_TAC "y:*"];
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC "y:*";
    DISJ1_TAC THEN MATCH_MP_TAC TC_INC] THEN
  ASM_REWRITE_TAC[]);;

let RTC_CASES_R = prove_thm(`RTC_CASES_R`,
  "!(R:*->*->bool) x z. RTC R x z = (x = z) \/ ?y. R x y /\ RTC R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC; RC_CASES] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o ONCE_REWRITE_RULE[TC_CASES_R]) THENL
     [DISJ2_TAC THEN EXISTS_TAC "z:*";
      FIRST_ASSUM(X_CHOOSE_TAC "y:*") THEN DISJ2_TAC THEN EXISTS_TAC "y:*"];
    DISJ1_TAC THEN MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC "y:*";
    DISJ1_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC TC_INC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[]);;

let RTC_INDUCT = prove_thm(`RTC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "TC(R:*->*->bool) x y" THEN
  RULE_INDUCT_TAC TC_INDUCT THEN
  FIRST_ASSUM(\th. MATCH_MP_TAC th THEN TRY(EXISTS_TAC "y:*") THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));;

let RTC_INDUCT_L = prove_thm(`RTC_INDUCT_L`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. P x y /\ R y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "TC(R:*->*->bool) x y" THEN
  RULE_INDUCT_TAC TC_INDUCT_L THEN
  FIRST_ASSUM(\th. MATCH_MP_TAC th THEN TRY(EXISTS_TAC "y:*") THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));;

let RTC_INDUCT_R = prove_thm(`RTC_INDUCT_R`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x z. (?y. R x y /\ P y z) ==> P x z) ==>
                !x y. RTC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "TC(R:*->*->bool) x y" THEN
  RULE_INDUCT_TAC TC_INDUCT_R THEN
  FIRST_ASSUM(\th. MATCH_MP_TAC th THEN TRY(EXISTS_TAC "y:*") THEN
  ASM_REWRITE_TAC[] THEN NO_TAC));;

let RTC_MONO = prove_thm(`RTC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RTC R x y ==> RTC S x y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_MONO THEN MATCH_MP_TAC TC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let RTC_CLOSED = prove_thm(`RTC_CLOSED`,
  "!R:*->*->bool. (RTC R = R) = (!x. R x x) /\
                                (!x z. (?y. R x y /\ R y z) ==> R x z)",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RTC_REFL; RTC_TRANS];
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[RTC_INC] THEN
    RULE_INDUCT_TAC RTC_INDUCT THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC "y:*" THEN
    ASM_REWRITE_TAC[]]);;

let RTC_IDEMP = prove_thm(`RTC_IDEMP`,
  "!R:*->*->bool. RTC(RTC R) = RTC R",
  REWRITE_TAC[RTC_CLOSED; RTC_REFL; RTC_TRANS]);;

let RTC_SYM = prove_thm(`RTC_SYM`,
  "!R:*->*->bool. (!x y. R x y ==> R y x) ==> (!x y. RTC R x y ==> RTC R y x)",
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RTC] THEN
  MATCH_MP_TAC RC_SYM THEN MATCH_MP_TAC TC_SYM THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Symmetric transitive closure                                               %
%----------------------------------------------------------------------------%

let STC = new_definition(`STC`,
  "!R:*->*->bool. STC(R) = TC(SC R)");;

let STC_INC = prove_thm(`STC_INC`,
  "!(R:*->*->bool) x y. R x y ==> STC R x y",
  REPEAT STRIP_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_INC THEN MATCH_MP_TAC SC_INC THEN
  ASM_REWRITE_TAC[]);;

let STC_SYM = prove_thm(`STC_SYM`,
  "!(R:*->*->bool) x y. STC R x y ==> STC R y x",
  GEN_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_SYM THEN REWRITE_TAC[SC_SYM]);;

let STC_TRANS = prove_thm(`STC_TRANS`,
  "!(R:*->*->bool) x z. (?y. STC R x y /\ STC R y z) ==> STC R x z",
  REWRITE_TAC[STC; TC_TRANS]);;

let STC_TRANS_L = prove_thm(`STC_TRANS_L`,
  "!(R:*->*->bool) x z. (?y. STC R x y /\ R y z) ==> STC R x z",
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]);;

let STC_TRANS_R = prove_thm(`STC_TRANS_R`,
  "!(R:*->*->bool) x z. (?y. R x y /\ STC R y z) ==> STC R x z",
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SC_INC THEN ASM_REWRITE_TAC[]);;

let STC_CASES = prove_thm(`STC_CASES`,
  "!(R:*->*->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. STC R x y /\ STC R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  SUBGOAL_THEN "TC(SC(R:*->*->bool)) z x = TC(SC R) x z" SUBST1_TAC THENL
   [SPEC_TAC("x:*","x:*") THEN SPEC_TAC("z:*","z:*") THEN
    REWRITE_TAC[GSYM SYM_ALT] THEN MATCH_MP_TAC TC_SYM THEN
    MATCH_ACCEPT_TAC SC_SYM;
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]
  THENL
   [MATCH_MP_TAC TC_INC THEN MATCH_MP_TAC SC_INC;
    MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC "y:*"] THEN
  ASM_REWRITE_TAC[]);;

let STC_CASES_L = prove_thm(`STC_CASES_L`,
  "!(R:*->*->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. STC R x y /\ R y z",
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THENL
   [MATCH_MP_TAC STC_TRANS THEN EXISTS_TAC "y:*" THEN
    CONJ_TAC THEN MATCH_MP_TAC STC_SYM;
    MATCH_MP_TAC STC_SYM THEN MATCH_MP_TAC STC_TRANS_L THEN
    EXISTS_TAC "y:*"] THEN
  ASM_REWRITE_TAC[]);;

let STC_CASES_R = prove_thm(`STC_CASES_R`,
  "!(R:*->*->bool) x z. STC R x z = R x z \/ STC R z x \/
                                    ?y. R x y /\ STC R y z",
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISJ2_TAC THEN DISJ1_TAC THENL
   [MATCH_MP_TAC STC_TRANS THEN EXISTS_TAC "y:*" THEN
    CONJ_TAC THEN MATCH_MP_TAC STC_SYM;
    MATCH_MP_TAC STC_SYM THEN MATCH_MP_TAC STC_TRANS_R THEN
    EXISTS_TAC "y:*"] THEN
  ASM_REWRITE_TAC[]);;

let STC_INDUCT = prove_thm(`STC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x y. P x y ==> P y x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. STC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[STC] THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [UNDISCH_TAC "SC(R:*->*->bool) x y" THEN REWRITE_TAC[SC_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(ANTE_RES_THEN ACCEPT_TAC);
    FIRST_ASSUM(\th. MATCH_MP_TAC th THEN EXISTS_TAC "y:*") THEN
    ASM_REWRITE_TAC[]]);;

let STC_MONO = prove_thm(`STC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. STC R x y ==> STC S x y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_MP_TAC SC_MONO THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let STC_CLOSED = prove_thm(`STC_CLOSED`,
  "!R:*->*->bool. (STC R = R) = (!x y. R x y ==> R y x) /\
                                (!x z. (?y. R x y /\ R y z) ==> R x z)",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[STC_SYM; STC_TRANS];
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[STC_INC] THEN
    RULE_INDUCT_TAC STC_INDUCT THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(\th. MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC);
      FIRST_ASSUM(\th. MATCH_MP_TAC th THEN EXISTS_TAC "y:*") THEN
      ASM_REWRITE_TAC[]]]);;

let STC_IDEMP = prove_thm(`STC_IDEMP`,
  "!R:*->*->bool. STC(STC R) = STC R",
  REWRITE_TAC[STC_CLOSED; STC_SYM; STC_TRANS]);;

let STC_REFL = prove_thm(`STC_REFL`,
  "!R:*->*->bool. (!x. R x x) ==> !x. STC R x x",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC STC_INC THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% Reflexive symmetric transitive closure (smallest equivalence relation)     %
%----------------------------------------------------------------------------%

let RSTC = new_definition(`RSTC`,
  "!R:*->*->bool. RSTC(R) = RC(TC(SC R))");;

let RSTC_INC = prove_thm(`RSTC_INC`,
  "!(R:*->*->bool) x y. R x y ==> RSTC R x y",
  REPEAT STRIP_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_INC; TC_INC; SC_INC] THEN
  ASM_REWRITE_TAC[]);;

let RSTC_REFL = prove_thm(`RSTC_REFL`,
  "!(R:*->*->bool) x. RSTC R x x",
  REWRITE_TAC[RSTC; RC_REFL]);;

let RSTC_SYM = prove_thm(`RSTC_SYM`,
  "!(R:*->*->bool) x y. RSTC R x y ==> RSTC R y x",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_SYM; TC_SYM] THEN
  REWRITE_TAC[SC_SYM]);;

let RSTC_TRANS = prove_thm(`RSTC_TRANS`,
  "!(R:*->*->bool) x z. (?y. RSTC R x y /\ RSTC R y z) ==> RSTC R x z",
  REWRITE_TAC[RSTC; RC_TC; TC_TRANS]);;

let RSTC_TRANS_L = prove_thm(`RSTC_TRANS_L`,
  "!(R:*->*->bool) x z. (?y. RSTC R x y /\ R y z) ==> RSTC R x z",
  REWRITE_TAC[RSTC; RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_L THEN EXISTS_TAC "y:*" THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY MATCH_MP_TAC [RC_INC; SC_INC] THEN
  ASM_REWRITE_TAC[]);;

let RSTC_TRANS_R = prove_thm(`RSTC_TRANS_R`,
  "!(R:*->*->bool) x z. (?y. R x y /\ RSTC R y z) ==> RSTC R x z",
  REWRITE_TAC[RSTC; RC_TC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TC_TRANS_R THEN EXISTS_TAC "y:*" THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY MATCH_MP_TAC [RC_INC; SC_INC] THEN
  ASM_REWRITE_TAC[]);;

let RSTC_CASES = prove_thm(`RSTC_CASES`,
  "!(R:*->*->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ RSTC R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC; RC_TC; RC_SC] THEN
  REWRITE_TAC[GSYM STC] THEN
  GEN_REWRITE_TAC LAND_CONV [] [STC_CASES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [RC_CASES] THEN
  CONV_TAC(AC_CONV(DISJ_ASSOC,DISJ_SYM)));;

let RSTC_CASES_L = prove_thm(`RSTC_CASES_L`,
  "!(R:*->*->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. RSTC R x y /\ R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC; RC_CASES; GSYM STC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [STC_CASES_L] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISJ1_TAC] THEN REPEAT DISJ2_TAC THEN
  EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[]);;

let RSTC_CASES_R = prove_thm(`RSTC_CASES_R`,
  "!(R:*->*->bool) x z. RSTC R x z = (x = z) \/ R x z \/ RSTC R z x \/
                                     ?y. R x y /\ RSTC R y z",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSTC; RC_CASES; GSYM STC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [] [STC_CASES_R] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; DISJ1_TAC;
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
  REPEAT DISJ2_TAC THEN EXISTS_TAC "y:*" THEN ASM_REWRITE_TAC[]);;

let RSTC_INDUCT = prove_thm(`RSTC_INDUCT`,
  "!(R:*->*->bool) P.
        (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. P x y ==> P y x) /\
        (!x z. (?y. P x y /\ P y z) ==> P x z) ==>
                !x y. RSTC R x y ==> P x y",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RSTC] THEN
  RULE_INDUCT_TAC RC_INDUCT THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC "TC(SC(R:*->*->bool)) x y" THEN
  RULE_INDUCT_TAC TC_INDUCT THENL
   [UNDISCH_TAC "SC(R:*->*->bool) x y" THEN REWRITE_TAC[SC_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN (ANTE_RES_THEN MP_TAC)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(ANTE_RES_THEN ACCEPT_TAC);
    FIRST_ASSUM(\th. MATCH_MP_TAC th THEN EXISTS_TAC "y:*") THEN
    ASM_REWRITE_TAC[]]);;

let RSTC_MONO = prove_thm(`RSTC_MONO`,
  "!(R:*->*->bool) S.
        (!x y. R x y ==> S x y) ==>
        (!x y. RSTC R x y ==> RSTC S x y)",
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RSTC] THEN
  MAP_EVERY MATCH_MP_TAC [RC_MONO; TC_MONO; SC_MONO] THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let RSTC_CLOSED = prove_thm(`RSTC_CLOSED`,
  "!R:*->*->bool. (RSTC R = R) = (!x. R x x) /\
                                 (!x y. R x y ==> R y x) /\
                                 (!x z. (?y. R x y /\ R y z) ==> R x z)",
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[RSTC_REFL; RSTC_SYM; RSTC_TRANS];
    STRIP_TAC THEN REPEAT(CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
    EQ_TAC THEN REWRITE_TAC[RSTC_INC] THEN
    RULE_INDUCT_TAC RSTC_INDUCT THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(\th. MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC);
      FIRST_ASSUM(\th. MATCH_MP_TAC th THEN EXISTS_TAC "y:*") THEN
      ASM_REWRITE_TAC[]]]);;

let RSTC_IDEMP = prove_thm(`RSTC_IDEMP`,
  "!R:*->*->bool. RSTC(RSTC R) = RSTC R",
  REWRITE_TAC[RSTC_CLOSED; RSTC_REFL; RSTC_SYM; RSTC_TRANS]);;

%----------------------------------------------------------------------------%
% Finally, we prove the inclusion properties for composite closures          %
%----------------------------------------------------------------------------%

let RSC_INC_RC = prove_thm(`RSC_INC_RC`,
  "!R:*->*->bool. !x y. RC R x y ==> RSC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC; RC_SC; SC_INC]);;

let RSC_INC_SC = prove_thm(`RSC_INC_SC`,
  "!R:*->*->bool. !x y. SC R x y ==> RSC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[RSC; RC_INC]);;

let RTC_INC_RC = prove_thm(`RTC_INC_RC`,
  "!R:*->*->bool. !x y. RC R x y ==> RTC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC; RC_TC; TC_INC]);;

let RTC_INC_TC = prove_thm(`RTC_INC_TC`,
  "!R:*->*->bool. !x y. TC R x y ==> RTC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[RTC; RC_INC]);;

let STC_INC_SC = prove_thm(`STC_INC_SC`,
  "!R:*->*->bool. !x y. SC R x y ==> STC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[STC; TC_INC]);;

let STC_INC_TC = prove_thm(`STC_INC_TC`,
  "!R:*->*->bool. !x y. TC R x y ==> STC R x y",
  REPEAT GEN_TAC THEN REWRITE_TAC[STC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC SC_INC);;

let RSTC_INC_RC = prove_thm(`RSTC_INC_RC`,
  "!R:*->*->bool. !x y. RC R x y ==> RSTC R x y",
  REWRITE_TAC[RSTC; RC_TC; RC_SC; GSYM STC; STC_INC]);;

let RSTC_INC_SC = prove_thm(`RSTC_INC_SC`,
  "!R:*->*->bool. !x y. SC R x y ==> RSTC R x y",
  REWRITE_TAC[RSTC; GSYM RTC; RTC_INC]);;

let RSTC_INC_TC = prove_thm(`RSTC_INC_TC`,
  "!R:*->*->bool. !x y. TC R x y ==> RSTC R x y",
  GEN_TAC THEN REWRITE_TAC[RSTC; RC_TC; GSYM RSC] THEN
  MATCH_MP_TAC TC_MONO THEN MATCH_ACCEPT_TAC RSC_INC);;

let RSTC_INC_RSC = prove_thm(`RSTC_INC_RSC`,
  "!R:*->*->bool. !x y. RSC R x y ==> RSTC R x y",
  REWRITE_TAC[RSC; RSTC; RC_TC; TC_INC]);;

let RSTC_INC_RTC = prove_thm(`RSTC_INC_RTC`,
  "!R:*->*->bool. !x y. RTC R x y ==> RSTC R x y",
  GEN_TAC THEN REWRITE_TAC[GSYM RTC; RSTC] THEN MATCH_MP_TAC RTC_MONO THEN
  MATCH_ACCEPT_TAC SC_INC);;

let RSTC_INC_STC = prove_thm(`RSTC_INC_STC`,
  "!R:*->*->bool. !x y. STC R x y ==> RSTC R x y",
  GEN_TAC THEN REWRITE_TAC[GSYM STC; RSTC; RC_INC]);;

close_theory();;
