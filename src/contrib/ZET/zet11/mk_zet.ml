%< creates the theory of integers from
   a quotient construct>%

new_theory `zet`;; 

load_library `auxiliary`;;

load_library `quotient`;; 

load_library `convert`;;            

autoload_defs_and_thms `bool`;; 

autoload_defs_and_thms `prim_rec`;;


%<**************************DEFINITIONS*****************************>%

let ZET_REL = 
    new_definition(
    `ZET_REL`,
     "ZET_REL (m1:num,n1:num) (m2,n2) = ((m1 + n2) = (m2 + n1))");; 

let PRE_REV = 
   new_definition(
    `PRE_REV`,
    "PRE_REV (m1:num,n1:num) = (n1,m1)");;   

let PRE_PLUS =
   new_infix_definition(
    `PRE_PLUS`,
    "PRE_PLUS (m1,n1) (m2,n2) = (m1 + m2,n1 + n2)");;

let PRE_MULT =
   new_infix_definition(
    `PRE_MULT`,
    "PRE_MULT (m1,n1) (m2,n2) = ((m1 * m2) + (n1 * n2),(m1 * n2) + (m2 * n1))");;

%<************************FUNCTIONS**********************************>%

let COM_CONV = REWRITE_CONV ADD_SYM;;

let RL_CONV = REWRITE_CONV ADD_ASSOC;;

let LR_CONV = REWRITE_CONV (SYM(SPEC_ALL ADD_ASSOC));;

%<*************************THEOREMS**********************************>%

let w1 = "REFLEX ZET_REL";;

let thm1 = 
    prove(
    w1,
    REWRITE_TAC[REFLEX] THEN
    BETA_TAC THEN
    CONV_TAC PROD_CONV THEN
    REWRITE_TAC[ZET_REL]);;

let w2 = "SYMMETRY ZET_REL";;

let thm2 =
    prove(
    w2,
    REWRITE_TAC[SYMMETRY] THEN 
    BETA_TAC THEN
    CONV_TAC ((BINDER_CONV PROD_CONV) THENC PROD_CONV) THEN
    REWRITE_TAC[ZET_REL] THEN
    REPEAT STRIP_TAC THEN
    EQ_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[]);;  

let w3a = "!n m k. (n + k = m + k) = (n = m)";;

let INV_ADD = 
    prove(
    w3a,
    GEN_TAC THEN
    GEN_TAC THEN
    INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES] THEN 
    EQ_TAC THEN 
    STRIP_TAC THENL
      [IMP_RES_TAC INV_SUC THEN
       FILTER_RULE_ASSUM_TAC [3] SYM;ALL_TAC] THEN
    ASM_REWRITE_TAC[]);;

let w3b = "TRANSITIVITY ZET_REL";; 

let thm3 =
    prove(
    w3b,
    REWRITE_TAC[TRANSITIVITY] THEN
    BETA_TAC THEN
    CONV_TAC ((BINDER_CONV(BINDER_CONV PROD_CONV)) THENC 
              (BINDER_CONV PROD_CONV) THENC
               PROD_CONV) THEN
    REWRITE_TAC[ZET_REL] THEN 
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN "(x1 + y2) + (y1 + z2) = (z1 + y2) + (y1 + x2)" ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONV_TAC (LHS_CONV COM_CONV) THEN
      REWRITE_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN "(x1 + z2) + (y2 + y1) = (z1 + x2) + (y2 + y1)" ASSUME_TAC THENL
     [(CONV_TAC ((dir_CONV `fa` LR_CONV) THENC
                 (dir_CONV `faa` RL_CONV) THENC 
                 (dir_CONV `faafa` COM_CONV) THENC
                 (dir_CONV `faa` LR_CONV) THENC
                 (dir_CONV `faaa` COM_CONV) THENC
                 (dir_CONV `fa` RL_CONV) THENC
                 (dir_CONV `a` LR_CONV) THENC
                 (dir_CONV `aa` RL_CONV) THENC
                 (dir_CONV `aafa` COM_CONV) THENC
                 (dir_CONV `aa` LR_CONV) THENC
                 (dir_CONV `aaa` COM_CONV) THENC
                 (dir_CONV `a` RL_CONV)))  THEN
       ASM_REWRITE_TAC[];ALL_TAC] THEN
       RULE_ASSUM_TAC (REWRITE_RULE[INV_ADD]) THEN
       ASM_REWRITE_TAC[]);; 

let w4 = "EQUIVALENCE ZET_REL";; 

let EQUIVALENCE_ZET_REL =
    prove_thm(
    `EQUIVALENCE_ZET_REL`,
     w4,
     REWRITE_TAC[EQUIVALENCE] THEN
     BETA_TAC THEN
     REWRITE_TAC[thm1;thm2;thm3]);; 

let [thm_onto;thm_univ;thm_factor] = define_quotient_type(`zet`,EQUIVALENCE_ZET_REL);;

let ZET_FACTOR_TAC = FACTOR_TAC [thm_onto] [thm_univ];;  

let ZET_QUOTIENT_TAC =
     CONV_TAC (BASE_CHANGE_CONV thm_onto) THEN
     CONV_TAC PROD_CONV THEN
     (2 TIMES GEN_TAC);;

%<We start defining operations on `zet`.
  First of all REV (as INV is already in use>%

let w5 = "?!h.(PROJ_zet o PRE_REV) = h o PROJ_zet";;  

let thm5 =
    prove(
    w5,
    ZET_FACTOR_TAC THEN
    REWRITE_TAC[o_DEF] THEN
    BETA_TAC THEN 
    REWRITE_TAC[thm_univ] THEN
    REWRITE_TAC[PRE_REV;ZET_REL] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_REWRITE_TAC[]);;   

let thm6 = 
    let th1 = REWRITE_RULE[o_DEF] thm5 in
    let th2 = (CONV_RULE (BINDER_CONV (SYM_CONV THENC FUN_EQ_CONV))) th1 in
    let th3 = BETA_RULE th2 in
    let th4 = (CONV_RULE (BINDER_CONV PROD_CONV)) th3 in
    REWRITE_RULE[PRE_REV] th4;; 

%<***********************DEFINITIONS****************************************>%

let [REV;REV_UNIQUE] = new_unique_specification `REV` [`constant`,`REV`] thm6;;   

let INT = 
    new_definition(
    `INT`,
    "INT x = PROJ_zet (x,0)");; 

let ZERO =
    new_definition(
    `ZERO`,
    "zero = INT 0");;   

let ONE =
    new_definition(
    `ONE`,
    "een = INT 1");;   


let POS =
    new_definition(
    `POS`,
    "POS x = ?y.x = INT y");;    

let NEG = 
    new_definition(
    `NEG`,
    "NEG x = POS(REV x)");;

%<*************************THEOREMS**********************************>%

let w6 = "!x.REV(REV x) = x";; 

let REV2_ID = prove_thm(
    `REV2_ID`,
     w6,  
     ZET_QUOTIENT_TAC THEN   
     REWRITE_TAC[REV]);; 

let w7 = "ONE_ONE INT";;  

let INV_INT = prove_thm(
    `INV_INT`,
     w7,
     REWRITE_TAC[ONE_ONE_DEF;INT;thm_univ;ZET_REL;ADD_CLAUSES]);;
                                                                   

let w8 = "!n m.((m + m) = (n + n)) = (m = n)";; 

let PRE_INV_MULT = prove(
    w8,
    INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES;ADD_EQ_0];INDUCT_TAC] THENL
     [REWRITE_TAC[ADD_CLAUSES;(CONV_RULE (BINDER_CONV(RAND_CONV SYM_CONV))) NOT_SUC];
      EQ_TAC THEN STRIP_TAC] THENL
     [RULE_ASSUM_TAC (REWRITE_RULE[ADD_CLAUSES]) THEN
      IMP_RES_TAC INV_SUC THEN
      IMP_RES_TAC INV_SUC THEN
      REWRITE_RULE_ASSUM_TAC [1] [5];ALL_TAC] THEN
     ASM_REWRITE_TAC[]);;

let w9 = "!x.(REV x = x) = (x = zero)";; 

let FIX_REV = prove_thm(
    `FIX_REV`,
     w9,
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[REV;ZERO;INT;thm_univ;ZET_REL;ADD_CLAUSES;PRE_INV_MULT] THEN
     REPEAT GEN_TAC THEN 
     EQ_TAC THEN 
     STRIP_TAC THEN 
     ASM_REWRITE_TAC[]);;     

let w10 = "!x.(POS x) \/ (POS (REV x))";;  

let POS_PROP1 = prove_thm(
    `POS_PROP1`,
     w10,
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[REV;POS;INT;thm_univ;ZET_REL;ADD_CLAUSES] THEN
     DISJ_CASES_TAC (SPEC "y2:num"(SPEC "y1:num" LESS_CASES)) THENL
      [DISJ2_TAC THEN
       IMP_RES_TAC LESS_ADD THEN
       CONV_TAC (BINDER_CONV SYM_CONV);
       DISJ1_TAC THEN
       IMP_RES_TAC SUB_ADD THEN
       EXISTS_TAC "y1 - y2"] THEN 
     ASM_REWRITE_TAC[]);;   

let w11 = "!x.(POS x) /\ (POS (REV x)) ==> (x = zero)";;

let POS_PROP2 = prove_thm(
   `POS_PROP2`,
    w11,
    REWRITE_TAC[POS] THEN 
    REPEAT STRIP_TAC THEN
    REWRITE_RULE_ASSUM_TAC [1] [2] THEN
    FILTER_RULE_ASSUM_TAC [1] 
     (REWRITE_RULE[INT;REV;thm_univ;ZET_REL;ADD_CLAUSES]) THEN
    FILTER_RULE_ASSUM_TAC [1] SYM THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[ADD_EQ_0]) THEN
    ASM_REWRITE_TAC[ZERO]);; 

let w12 = "?!h.PROJ_zet o (\z.(FST z) PRE_PLUS (SND z)) = h o (PROJ_zet P PROJ_zet)";;
 
let thm12 = prove(
    w12,
    ZET_FACTOR_TAC THEN
    CONV_TAC PROD_CONV THEN 
    (4 TIMES GEN_TAC) THEN 
    CONV_TAC PROD_CONV THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[o_DEF] THEN 
    BETA_TAC THEN
    REWRITE_TAC[thm_univ;PRE_PLUS;ZET_REL] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC ((dir_CONV `fa` RL_CONV) THENC
              (dir_CONV `fafa` LR_CONV) THENC
              (dir_CONV `fafaa` COM_CONV) THENC
              (dir_CONV `fafa` RL_CONV) THENC
              (dir_CONV `fa` LR_CONV) THENC   
              (dir_CONV `a` RL_CONV) THENC
              (dir_CONV `afa` LR_CONV) THENC
              (dir_CONV `afaa` COM_CONV) THENC
              (dir_CONV `afa` RL_CONV) THENC
              (dir_CONV `a` LR_CONV)) THEN  
   ASM_REWRITE_TAC[]);;  

let thm13 = 
    let th1 = (CONV_RULE (BINDER_CONV (SYM_CONV THENC FUN_EQ_CONV THENC PROD_CONV))) thm12 in
    let th2 = (CONV_RULE (BINDER_CONV PROD_CONV)) th1 in
    let th3 = REWRITE_RULE[o_DEF;P] th2 in
    let th4 = BETA_RULE th3 in   
    let th5 = REWRITE_RULE[PRE_PLUS] th4 in
    let th6 = hd(CONJUNCTS CURRY_ISO) in
    let th7 = (CONV_RULE (BASE_CHANGE_CONV th6)) th5 in
    REWRITE_RULE[UNCURRY_DEF] th7;;


%<***********************DEFINITIONS****************************************>%   

let [PLUS;PLUS_UNIQUE] = new_unique_specification `PLUS` [`infix`,`plus`] thm13;;  

let MINUS = new_infix_definition(
    `MINUS`,
    "minus x y = x plus (REV y)");;  

let LEQ = new_infix_definition(
    `LEQ`,
    "leq x y = POS(y minus x)");;


%<*************************PLUS_THEOREMS**********************************>%

let w14 = "!x y.(INT x) plus (INT y) = (INT (x + y))";;

let INT_PLUS = prove_thm(
    `INT_PLUS`,
     w14,
     REWRITE_TAC[INT;PLUS;thm_univ;ZET_REL;ADD_CLAUSES]);;  

let w15 = "!x y.REV( x plus y) = ((REV x) plus (REV y))";;   

let REV_PLUS = prove_thm(
    `REV_PLUS`,
     w15, 
     (2 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[PLUS;REV]);; 

let w16 = "(!x.x plus zero = x) /\ (!x.zero plus x = x)";;   

let ZERO_PLUS = prove_thm(
    `ZERO_PLUS`,
     w16, 
     CONJ_TAC THEN
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[ZERO;INT;PLUS;thm_univ;ZET_REL;ADD_CLAUSES]);;

let w17 = "(!x.x plus (REV x) = zero) /\ (!x.(REV x) plus x = zero)";; 

let REV_PLUS_ZERO = prove_thm(
    `REV_PLUS_ZERO`,
     w17, 
     CONJ_TAC THEN
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[ZERO;INT;PLUS;REV;thm_univ;ZET_REL;ADD_CLAUSES] THEN
     REPEAT GEN_TAC THEN 
     CONV_TAC (LHS_CONV COM_CONV) THEN 
     REWRITE_TAC[]);; 

let w18 = "!x y.(x plus y) = (y plus x)";; 

let PLUS_COM = prove_thm(
    `PLUS_COM`,
     w18, 
     (2 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[PLUS;thm_univ;ZET_REL;ADD_CLAUSES] THEN
     CONV_TAC (LHS_CONV((LHS_CONV COM_CONV) THENC (RAND_CONV COM_CONV))) THEN
     REWRITE_TAC[]);; 

let w19 = "!x y z.x plus (y plus z) = ((x plus y) plus z)";;  

let PLUS_ASSOC = prove_thm(
    `PLUS_ASSOC`,
     w19,
     (3 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[PLUS;thm_univ;ZET_REL;ADD_ASSOC]);; 

let w20 = "(!x y.x plus (y minus x) = y) /\
           (!x y.(y minus x) plus x = y)";;  

let MINUS_PROP = prove_thm(
   `MINUS_PROP`,
    w20,
    CONJ_TAC THENL
    [ONCE_REWRITE_TAC[PLUS_COM];ALL_TAC] THEN
    REWRITE_TAC[MINUS;SYM(SPEC_ALL PLUS_ASSOC);REV_PLUS_ZERO;ZERO_PLUS]);;  

let w21 = "!k.ISO ($plus k)";; 

let ISO_PLUS_K = prove_thm(
   `ISO_PLUS_K`,
    w21,
    GEN_TAC THEN
    SUBGOAL_THEN "(!x. k plus ((REV k) plus x) = x) /\  
                  (!x. (REV k) plus (k plus x) = x)" STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS];
      IMP_RES_TAC ID_ISO]);;   


%<*************************LEQ_THEOREMS**********************************>%
 
let w22 = "!x.x leq x";;

let REFLEX_LEQ = prove_thm(
   `REFLEX_LEQ`,
    w22,
    REWRITE_TAC[LEQ;MINUS;REV_PLUS_ZERO;ZERO;SPEC "0" (MATCH_MP DEF_THM1 POS)]);;

let w23 = "!x y. (x leq y) /\ (y leq x) ==> (x = y)";;

let ANTI_SYM_LEQ = prove_thm(
   `ANTI_SYM_LEQ`,
    w23,
    REWRITE_TAC[LEQ;MINUS] THEN 
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN "(x plus (REV y)) = REV(y plus (REV x))" ASSUME_TAC THENL
                [REWRITE_TAC[REV_PLUS;REV2_ID] THEN
                 CONV_TAC (LHS_CONV (REWRITE_CONV PLUS_COM)) THEN
                 REWRITE_TAC[];ALL_TAC] THEN
    REWRITE_RULE_ASSUM_TAC [2] [1] THEN
    IMP_RES_TAC POS_PROP2 THEN
    FILTER_RULE_ASSUM_TAC [1] (AP_TERM "$plus") THEN
    FILTER_RULE_ASSUM_TAC [1] (\th.AP_THM  th "x:zet") THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE
                           [SYM(SPEC_ALL  PLUS_ASSOC);REV_PLUS_ZERO;ZERO_PLUS]) THEN
    ASM_REWRITE_TAC[]);; 

%<********************AUXILIARIES**********************************>%  

let COM_CONV = REWRITE_CONV PLUS_COM;;

let RL_CONV = REWRITE_CONV PLUS_ASSOC;;

let LR_CONV = REWRITE_CONV (SYM(SPEC_ALL PLUS_ASSOC));; 

let MK_MULT [th1;th2] = MK_COMB ((AP_TERM "$*" th1),th2);;

let MK_ADD [th1;th2] = MK_COMB ((AP_TERM "$+" th1),th2);; 

let MK_PLUS [th1;th2] = MK_COMB ((AP_TERM "$plus" th1),th2);;

let CP = REWRITE_CONV ADD_SYM;;

let CM = REWRITE_CONV MULT_SYM;;

let RL = REWRITE_CONV ADD_ASSOC;;

let LR = REWRITE_CONV (SYM(SPEC_ALL ADD_ASSOC));;  

let RLM = REWRITE_CONV MULT_ASSOC;;

let LRM = REWRITE_CONV (SYM(SPEC_ALL MULT_ASSOC));;  

let cp = REWRITE_CONV PLUS_COM;;
 
let rl = REWRITE_CONV PLUS_ASSOC;;

let lr = REWRITE_CONV (SYM(SPEC_ALL PLUS_ASSOC));;


letrec DIR_CONV convlist  =
  if (convlist = []) then
                           ALL_CONV
  else 
     (let str,conv = hd convlist in
       (dir_CONV str conv) THENC (DIR_CONV (tl convlist)));;  

let ISO_REV = CONJUNCT1(MATCH_MP ID_ISO (CONJ REV2_ID REV2_ID));;  

%<*************************LEQ_THEOREMS**********************************>%

let w24 = "!x y z.(x leq y) /\ (y leq z) ==> (x leq z)";;

let TRANSITIVITY_LEQ = prove_thm(
   `TRANSITIVITY_LEQ`,
    w24,
    REWRITE_TAC[LEQ;MINUS;POS] THEN 
    REPEAT STRIP_TAC THEN
    EXISTS_TAC "y'' + y'" THEN
    FILTER_ASSUM_LIST [1;2] 
          (\[th1;th2].ASSUME_TAC (MK_COMB ((AP_TERM "$plus" th1),th2))) THEN
    FILTER_RULE_ASSUM_TAC [1] (CONV_RULE (
                             (dir_CONV `fa` LR_CONV) THENC
                             (dir_CONV `faa` RL_CONV))) THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[REV_PLUS_ZERO;INT_PLUS;ZERO_PLUS]) THEN
    ASM_REWRITE_TAC[]);;

let w25 ="!x y.(x leq y) \/ (y leq x)";;  

let LINEAR_LEQ = prove_thm(
   `LINEAR_LEQ`,
    w25,
    REWRITE_TAC[LEQ;MINUS] THEN
    REPEAT STRIP_TAC THEN  
    SUBGOAL_THEN "(x plus (REV y)) = REV(y plus (REV x))" ASSUME_TAC THENL
                [REWRITE_TAC[REV_PLUS;REV2_ID] THEN
                 CONV_TAC (LHS_CONV (REWRITE_CONV PLUS_COM)) THEN
                 REWRITE_TAC[];ALL_TAC] THEN 
    ASM_REWRITE_TAC[POS_PROP1]);;

let w26 = "!x y z.( x leq y) ==> ((x plus z) leq (y plus z))";; 

let TRANSLATION_LEQ = prove_thm(
   `TRANSLATION_LEQ`,
    w26,
    REWRITE_TAC[LEQ;MINUS;POS] THEN 
    REPEAT STRIP_TAC THEN
    EXISTS_TAC "y':num" THEN
    REWRITE_TAC[REV_PLUS] THEN
    CONV_TAC ((dir_CONV `faa` COM_CONV) THENC
              (dir_CONV `fa` LR_CONV) THENC
              (dir_CONV `faa` RL_CONV)) THEN
    ASM_REWRITE_TAC[REV_PLUS_ZERO;ZERO_PLUS]);; 

let w27 = "!x y.((INT x) leq (INT y)) = (x <= y)";; 

let INT_LEQ = prove_thm(
   `INT_LEQ`,
    w27,
    REWRITE_TAC[LEQ;MINUS;POS] THEN 
    REPEAT STRIP_TAC THEN 
    EQ_TAC THEN 
    REPEAT STRIP_TAC THENL
     [RULE_ASSUM_TAC (AP_TERM "$plus") THEN
      RULE_ASSUM_TAC (\th.AP_THM th "INT x") THEN
      RULE_ASSUM_TAC 
        (REWRITE_RULE[SYM(SPEC_ALL PLUS_ASSOC);REV_PLUS_ZERO;ZERO_PLUS;INT_PLUS]) THEN
      IMP_RES_TAC (REWRITE_RULE[ONE_ONE_DEF] INV_INT) THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[LESS_EQ_ADD];
      IMP_RES_TAC SUB_ADD THEN
      EXISTS_TAC "y - x" THEN
      FILTER_RULE_ASSUM_TAC [1] (AP_TERM "INT") THEN
      FILTER_RULE_ASSUM_TAC [1] SYM THEN
      ASM_REWRITE_TAC[SYM(SPEC_ALL INT_PLUS);SYM(SPEC_ALL PLUS_ASSOC);
                                             REV_PLUS_ZERO;ZERO_PLUS]
    ]);;

let w28= "~(zero = een) /\ ~(een = zero)";; 

let ZERO_NOT_ONE = prove_thm(
   `ZERO_NOT_ONE`,
    w28,
    REWRITE_TAC[ZERO;ONE;INT;thm_univ;ZET_REL;ADD_CLAUSES] THEN
    CONV_TAC (LHS_CONV(RAND_CONV SYM_CONV)) THEN
    REWRITE_TAC[num_CONV "1";NOT_SUC]);;

let w29 ="(!x.zero leq (INT x)) /\ (!x.(REV(INT x)) leq zero)";;

let LEQ_CLAUSES = prove_thm(
   `LEQ_CLAUSES`,
    w29,
    REWRITE_TAC[LEQ;MINUS;REWRITE_RULE[] (SPEC "zero" FIX_REV);ZERO_PLUS;REV2_ID] THEN
    REWRITE_TAC[MATCH_MP DEF_THM1 POS]);;

let w30 = "!x y.(x leq y) = ((REV y) leq (REV x))";; 

let REV_LEQ = prove_thm(
   `REV_LEQ`,
    w30,
    REWRITE_TAC[LEQ;MINUS;REV2_ID] THEN
    REPEAT GEN_TAC THEN 
    AP_TERM_TAC THEN
    CONV_TAC (LHS_CONV (REWRITE_CONV PLUS_COM)) THEN
    REWRITE_TAC[]);; 

let w31 = "!x. ((x minus een) leq x) /\ (x leq (x plus een))";; 

let ONE_LEQ = prove_thm(
   `ONE_LEQ`,
    w31,
    REWRITE_TAC[LEQ;MINUS;REV_PLUS;REV2_ID] THEN
    REPEAT GEN_TAC THEN 
    CONV_TAC (RAND_CONV(RAND_CONV(REWRITE_CONV PLUS_COM))) THEN
    REWRITE_TAC[PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS;ONE] THEN
    REWRITE_TAC[MATCH_MP DEF_THM1 POS]);; 

let w32 = "!x.~((x minus een) = x) /\ ~((x plus een) = x)";; 
 
let ONE_PROPER_LEQ = prove_thm(
   `ONE_PROPER_LEQ`,
    w32,
    REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC (\th.MK_PLUS [REFL "REV x";th]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[MINUS;PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS]) THENL
      [RULE_ASSUM_TAC (\th.REWRITE_RULE[REV2_ID] (AP_TERM "REV" th)) THEN
       RULE_ASSUM_TAC (REWRITE_RULE[REWRITE_RULE[] (SPEC "zero" FIX_REV)]);
       ALL_TAC] THEN
    IMP_RES_TAC ZERO_NOT_ONE);; 

let w33 = "!x. ((een leq x) \/ (x leq (REV een))) ==> ~(x = zero)";;

let ZERO_LEQ_ONE = prove_thm(
   `ZERO_LEQ_ONE`,
    w33,
    REPEAT STRIP_TAC THEN
    REWRITE_RULE_ASSUM_TAC [2] [1] THENL
     [ASSUME_TAC (REWRITE_RULE[ZERO_PLUS](CONJUNCT2(SPEC "zero" ONE_LEQ)));
      ASSUME_TAC (REWRITE_RULE[MINUS;ZERO_PLUS](CONJUNCT1(SPEC "zero" ONE_LEQ)))] THEN
    IMP_RES_TAC ANTI_SYM_LEQ THENL
     [ALL_TAC;
      FILTER_RULE_ASSUM_TAC [1] (\th.REWRITE_RULE[REV2_ID] (AP_TERM "REV" th)) THEN
      FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[REWRITE_RULE[] (SPEC "zero" FIX_REV)])] THEN
    IMP_RES_TAC ZERO_NOT_ONE);; 


 


%<********************ZET_INDUCTION_THEOREM***********************************>%

let w34 = "!Q.((!x.(NEG x) ==> Q x) /\ (!x.((POS x) /\ (Q x)) ==> 
                                              (Q (x plus een)))) ==> !x.Q x";; 

let ZET_INDUCTION0 = prove_thm(
    `ZET_INDUCTION0`,
     w34,
     REPEAT STRIP_TAC THEN
     DISJ_CASES_TAC (SPEC "x:zet" POS_PROP1) THENL
      [ALL_TAC;
       RULE_ASSUM_TAC (REWRITE_RULE[NEG]) THEN
       RES_TAC] THEN
     SUBGOAL_THEN "!x.Q (INT x)" ASSUME_TAC THENL
      [INDUCT_TAC;ALL_TAC] THENL
      [SUBGOAL_THEN "NEG zero" ASSUME_TAC;ALL_TAC;ALL_TAC] THENL
      [REWRITE_TAC[NEG] THEN
       REWRITE_TAC[REWRITE_RULE[] (SPEC "zero" FIX_REV)] THEN
       REWRITE_TAC[POS] THEN
       EXISTS_TAC "0" THEN
       REWRITE_TAC[ZERO];
       RES_TAC THEN
       RULE_ASSUM_TAC (REWRITE_RULE[ZERO]) THEN
       ASM_REWRITE_TAC[]; 
       ASSUME_TAC (MATCH_MP DEF_THM1 POS) THEN
       FILTER_RULE_ASSUM_TAC [4] (SPEC "INT x'") THEN
       REWRITE_RULE_ASSUM_TAC [4] [1] THEN
       RES_TAC THEN
       RULE_ASSUM_TAC (REWRITE_RULE[ONE;INT_PLUS]) THEN
       ASM_REWRITE_TAC[ADD1];
       FILTER_ASSUM_TAC [2] UNDISCH_TAC THEN
       REWRITE_TAC[POS] THEN 
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC[]]);;


%<**************************TACTIC(AL)S*******************************>%


let ZET_INDUCT0_TAC (A,t) = 
    (let th = ZET_INDUCTION0 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in
     let tac = 
     (MATCH_MP_TAC thm THEN  
      CONJ_TAC THEN
      FIRST[CONV_TAC (BINDER_CONV((RAND_CONV BETA_CONV) THENC
                                  (LHS_CONV(RAND_CONV BETA_CONV))));
            CONV_TAC (BINDER_CONV(RAND_CONV BETA_CONV))] )in
      tac (A,t));;

%<********************ZET_INDUCTION_THEOREM***********************************>%

let w35 = "!k Q.((!x.(x leq k) ==> (Q x)) /\
                 (!x.((k leq x) /\ (Q x)) ==> (Q (x plus een)))) ==> (!x.Q x)";;
     
let ZET_INDUCTION1 = prove_thm(
   `ZET_INDUCTION1`,
    w35,
    REWRITE_TAC[LEQ;MINUS] THEN 
    REPEAT STRIP_TAC THEN 
    SPEC_TAC ("x:zet","x:zet") THEN
    CONV_TAC (BASE_CHANGE_CONV (SPEC "k:zet" ISO_PLUS_K)) THEN
    ZET_INDUCT0_TAC THEN
    CONV_TAC (BASE_CHANGE_CONV (SPEC "REV k:zet" ISO_PLUS_K)) THEN
    REWRITE_TAC[NEG;PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS;REV_PLUS;REV2_ID] THENL
     [ASM_REWRITE_TAC[];
      CONV_TAC (BINDER_CONV(LHS_CONV (once_rewrite_CONV [PLUS_COM]))) THEN
      ASM_REWRITE_TAC[]]);; 

%<**************************TACTIC(AL)S*******************************>%

%<The parameter k in the tactic below determines the
  point where induction really starts>%



let ZET_INDUCT1_TAC k (A,t) = 
    (let th = SPEC k ZET_INDUCTION1 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in 
     let PART_MATCH' partfn th =
              (let pth = GSPEC th  in
               let pat = partfn(concl pth) in
               let matchfn = match pat in
               \tm. INST_TY_TERM (matchfn tm) pth) in  
     let MATCH_MP_TAC' thm:tactic (gl,g) =
              (let imp = ((PART_MATCH' (snd o dest_imp) thm) g) ? 
	       failwith `MATCH_MP_TAC` in
    
               ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl))) in
     let tac = 
     (MATCH_MP_TAC' thm THEN
      REPEAT CONJ_TAC THEN
      GEN_TAC THENL
      [CONV_TAC (RAND_CONV BETA_CONV);
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)))] THEN
      REPEAT STRIP_TAC) in
     tac (A,t));;  

%<********************ZET_INDUCTION_THEOREMS***********************************>%

let w36 = "!k Q.((Q k) /\ (!x.((k leq x) /\ (Q x)) ==> (Q (x plus een)))) ==> 
                    (!x.(k leq x) ==> (Q x))";; 

let thm36 = prove(
    w36,
    2 TIMES GEN_TAC THEN
    STRIP_TAC THEN
    ZET_INDUCT1_TAC "k:zet" THENL
     [IMP_RES_TAC ANTI_SYM_LEQ THEN
      SUB_ASSUM_TAC [1;8] THEN
      ASM_REWRITE_TAC[];
      RES_TAC]);;  



let w37 = "!k Q.((Q k) /\ (!x.((x leq k) /\ (Q x)) ==> (Q (x minus een)))) ==> 
                    (!x.(x leq k) ==> (Q x))";; 

let thm37 = prove(
    w37,
    2 TIMES GEN_TAC THEN
    STRIP_TAC THEN
    CONV_TAC (BASE_CHANGE_CONV ISO_REV) THEN
    FILTER_RULE_ASSUM_TAC [1] (CONV_RULE (BASE_CHANGE_CONV ISO_REV)) THEN
    ZET_INDUCT1_TAC "REV k" THENL
     [RULE_ASSUM_TAC (REWRITE_RULE[LEQ;MINUS;REV2_ID;SYM(SPEC_ALL REV_PLUS)]) THEN  
      IMP_RES_TAC POS_PROP2 THEN
      SUB_ASSUM_TAC [1;7] THEN
      FILTER_RULE_ASSUM_TAC [1] (\th.MK_PLUS [REFL "REV k";th]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE[PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS]) THEN
      ASM_REWRITE_TAC[REV2_ID];
      RULE_ASSUM_TAC (REWRITE_RULE[LEQ;MINUS;REV2_ID]) THEN
      REWRITE_TAC[REV_PLUS] THEN
      FILTER_RULE_ASSUM_TAC [3] (CONV_RULE (RAND_CONV (REWRITE_CONV PLUS_COM))) THEN
      RES_TAC]);;

let w38 = "!k Q.((Q k) /\ 
                  (!x.((x leq k) /\ (Q x)) ==> (Q (x minus een))) /\
                  (!x.((k leq x) /\ (Q x)) ==> (Q (x plus een)))) ==> 
                    (!x.Q x)";; 

let ZET_INDUCTION2 = prove_thm(
   `ZET_INDUCTION2`,
    w38,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (SPEC "x:zet"(SPEC "k:zet" LINEAR_LEQ)) THENL
     [IMP_RES_TAC thm36;
      IMP_RES_TAC thm37]);;  

%<**************************TACTIC(AL)S*******************************>%

%<The parameter k in the tactic below determines the
  point where induction really starts>%

let ZET_INDUCT2_TAC k (A,t) = 
    (let th = SPEC k ZET_INDUCTION2 in
     let x,body = dest_forall t in
     let tyi = snd(match (fst(dest_forall (concl th))) "\^x.T") in
     let spec = SPEC (mk_abs(x,body)) (INST_TYPE tyi th) in
     let spec' = DISCH_ALL (CONV_RULE (GEN_ALPHA_CONV x) (UNDISCH spec)) in
     let thm = CONV_RULE(RAND_CONV(BINDER_CONV BETA_CONV)) spec' in 
     let PART_MATCH' partfn th =
              (let pth = GSPEC th  in
               let pat = partfn(concl pth) in
               let matchfn = match pat in
               \tm. INST_TY_TERM (matchfn tm) pth) in  
     let MATCH_MP_TAC' thm:tactic (gl,g) =
              (let imp = ((PART_MATCH' (snd o dest_imp) thm) g) ? 
	       failwith `MATCH_MP_TAC` in
    
               ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl))) in
     let tac = 
     (MATCH_MP_TAC' thm THEN
      REPEAT CONJ_TAC THENL
      [ALL_TAC;GEN_TAC;GEN_TAC] THENL
      [CONV_TAC BETA_CONV;
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)));
       CONV_TAC ((RAND_CONV BETA_CONV) THENC
                 (LHS_CONV(RAND_CONV BETA_CONV)))] THEN
      REPEAT STRIP_TAC) in
     tac (A,t));; 

let w39 = "!f:*->**.ONE_ONE f ==>(!z.(@y.f z = f y) = z)";; 

let PRE_LIFT_THM = prove(
    w39,
    REWRITE_TAC[ONE_ONE_DEF] THEN 
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN "?y:*.(f z = (f y:**))" ASSUME_TAC THENL
    [EXISTS_TAC "z:*" THEN REWRITE_TAC[];ALL_TAC] THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[EXISTS_DEF]) THEN
    FILTER_RULE_ASSUM_TAC [1] (SYM o BETA_RULE) THEN
    RES_TAC);;  

let w40 = "!f:*->**.ONE_ONE f ==>((!z.(@y.f z = f y) = z) /\
                                (!z.(@y.f y = f z) = z))";;

let LIFT_THM = prove(
    w40,
    GEN_TAC THEN
    STRIP_TAC THEN
    CONJ_TAC THENL  
    [ALL_TAC;CONV_TAC (BINDER_CONV(LHS_CONV(BINDER_CONV SYM_CONV)))] THEN
    IMP_RES_TAC PRE_LIFT_THM);; 

let INT_LIFT_THM = MATCH_MP LIFT_THM INV_INT;;

let w41 ="!k (c:*) fd fu.?f.((f k) = c) /\ 
                       (!x.(x leq k) ==> ((f (x minus een)) = (fd (f x) x))) /\
                       (!x.(k leq x) ==> ((f (x plus een)) = (fu (f x) x)))";; 

let ZET_REC_THM = prove_thm(
   `ZET_REC_THM`,
    w41,
    REPEAT GEN_TAC THEN
    DEFINE "Fu = \y:*.\n.fu y ((INT n) plus k):*" THEN
    DEFINE "Gu = PRIM_REC (c:*) Fu" THEN
    ASSUME_TAC (SPEC "Fu:* -> num -> *"(SPEC "c:*" PRIM_REC_THM)) THEN
    FILTER_RULE_ASSUM_TAC [2] SYM THEN
    REWRITE_RULE_ASSUM_TAC [1] [2] THEN
    REWRITE_RULE_ASSUM_TAC [1] [3] THEN
    FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[ADD1]) THEN  
    DEFINE "gu = \x.Gu (@z.(x minus k) = INT z):*" THEN
    SUBGOAL_THEN "!x.(k leq x) ==> ((gu (x plus een):*) = fu (gu x) x)"   
                                                            ASSUME_TAC THENL
    [REWRITE_TAC[LEQ;POS] THEN 
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     SUBGOAL_THEN "(x plus een) minus k = INT (y + 1)" ASSUME_TAC THENL
       [REWRITE_TAC[MINUS] THEN
        CONV_TAC (DIR_CONV [`fa`,lr;`faa`,cp;`fa`,rl]) THEN
        RULE_ASSUM_TAC (REWRITE_RULE[MINUS]) THEN
        ASM_REWRITE_TAC[ONE;INT_PLUS];ALL_TAC] THEN
     ASM_REWRITE_TAC[INT_LIFT_THM] THEN
     FILTER_RULE_ASSUM_TAC [2] SYM THEN
     ASM_REWRITE_TAC[MINUS_PROP];ALL_TAC] THEN
    SUBGOAL_THEN "gu (k:zet) = c:*" ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC[MINUS;REV_PLUS_ZERO;ZERO;INT_LIFT_THM];ALL_TAC] THEN
    SUB_ASSUM_TAC[1;2] THEN
    DEFINE "Fd = \y:*.\n.fd y (k minus (INT n)):*" THEN
    DEFINE "Gd = PRIM_REC (c:*) Fd" THEN
    ASSUME_TAC (SPEC "Fd:* -> num -> *"(SPEC "c:*" PRIM_REC_THM)) THEN
    FILTER_RULE_ASSUM_TAC [2] SYM THEN
    REWRITE_RULE_ASSUM_TAC [1] [2] THEN
    REWRITE_RULE_ASSUM_TAC [1] [3] THEN
    FILTER_RULE_ASSUM_TAC [1] BETA_RULE THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[ADD1]) THEN  
    DEFINE "gd = \x.Gd (@z.(k minus x) = INT z):*" THEN
    SUBGOAL_THEN "!x.(x leq k) ==> ((gd (x minus een):*) = fd (gd x) x)"   
                                                            ASSUME_TAC THENL  
    [REWRITE_TAC[LEQ;POS] THEN 
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     SUBGOAL_THEN "k minus (x minus een) = INT (y + 1)" ASSUME_TAC THENL
       [REWRITE_TAC[MINUS;REV_PLUS;REV2_ID;PLUS_ASSOC] THEN
        RULE_ASSUM_TAC (REWRITE_RULE[MINUS]) THEN
        ASM_REWRITE_TAC[ONE;INT_PLUS];ALL_TAC] THEN
     ASM_REWRITE_TAC[INT_LIFT_THM] THEN
     FILTER_RULE_ASSUM_TAC [2] SYM THEN
     ASM_REWRITE_TAC[MINUS;REV_PLUS;REV2_ID;PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS];
                                                                 ALL_TAC] THEN
    SUBGOAL_THEN "gd (k:zet) = c:*" ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC[MINUS;REV_PLUS_ZERO;ZERO;INT_LIFT_THM];ALL_TAC] THEN     
    SUB_ASSUM_TAC[1;2;7;8] THEN
    DEFINE "h = \x.((k leq x) => ((gu x):*) | (gd x))" THEN
    SUBGOAL_THEN "!x.(k leq x) ==> (h x = (gu x:*))" ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC[];ALL_TAC] THEN
    SUBGOAL_THEN "!x.(x leq k) ==> (h x = (gd x:*))" ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN
     ASM_CASES_TAC "x = (k:zet)" THENL
      [ASSUME_TAC (SPEC "k:zet" REFLEX_LEQ) THEN
       ASM_REWRITE_TAC[] THEN
       BETA_TAC THEN ASM_REWRITE_TAC[];ALL_TAC] THEN
     ASM_CASES_TAC "k leq x" THENL
      [IMP_RES_TAC ANTI_SYM_LEQ THEN RES_TAC;ALL_TAC] THEN  
     ASM_REWRITE_TAC[] THEN
     BETA_TAC THEN
     ASM_REWRITE_TAC[];ALL_TAC] THEN
    SUB_ASSUM_TAC [1;2;4;5;6;7] THEN
    EXISTS_TAC "h:zet->*" THEN
    REPEAT STRIP_TAC THENL
    [ASSUME_TAC (SPEC "k:zet" REFLEX_LEQ) THEN RES_TAC THEN ASM_REWRITE_TAC[];
     STRIP_ASSUME_TAC (SPEC "x:zet" ONE_LEQ) THEN
     IMP_RES_TAC TRANSITIVITY_LEQ THEN
     RES_TAC THEN ASM_REWRITE_TAC[];
     STRIP_ASSUME_TAC (SPEC "x:zet" ONE_LEQ) THEN
     IMP_RES_TAC TRANSITIVITY_LEQ THEN
     RES_TAC THEN ASM_REWRITE_TAC[]]);;

let w42 ="!k (c:*) fd fu.?!f.((f k) = c) /\ 
                       (!x.(x leq k) ==> ((f (x minus een)) = (fd (f x) x))) /\
                       (!x.(k leq x) ==> ((f (x plus een)) = (fu (f x) x)))";; 
                                        
let zet_Axiom = prove_thm(
   `zet_Axiom`,
    w42,
    REPEAT GEN_TAC THEN
    CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
    [REWRITE_TAC[ZET_REC_THM]; 
     BETA_TAC THEN
     REPEAT STRIP_TAC THEN
     CONV_TAC FUN_EQ_CONV THEN
     ZET_INDUCT2_TAC "k:zet" THEN 
     RES_TAC THEN 
     ASM_REWRITE_TAC []]);;  
                                                                           

let w43 = "!k x. (x leq k) \/ ((k plus een) leq x)";;

let DISCRETE_ZET = prove_thm(
   `DISCRETE_ZET`,
    w43,
    GEN_TAC THEN
    ZET_INDUCT2_TAC "k:zet" THENL
      [REWRITE_TAC[REFLEX_LEQ];
       ASSUME_TAC (CONJUNCT1 (SPEC "x:zet" ONE_LEQ)) THEN
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       ASM_REWRITE_TAC[];
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       SUB_ASSUM_TAC [1] THEN
       NEW_IMP_RES_TAC TRANSLATION_LEQ THEN
       FILTER_RULE_ASSUM_TAC [1] (SPEC "REV k:zet") THEN
       FILTER_RULE_ASSUM_TAC [1] (ONCE_REWRITE_RULE[PLUS_COM]) THEN
       FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[PLUS_ASSOC;REV_PLUS_ZERO;ZERO_PLUS]) THEN
       ASSUME_TAC (REWRITE_RULE[ZERO_PLUS] (CONJUNCT2 (SPEC "zero" ONE_LEQ))) THEN
       SUB_ASSUM_TAC [1;2] THEN
       IMP_RES_TAC ANTI_SYM_LEQ THEN
       IMP_RES_TAC ZERO_NOT_ONE;
       IMP_RES_TAC ANTI_SYM_LEQ THEN
       SUB_ASSUM_TAC [1] THEN 
       ASM_REWRITE_TAC[REFLEX_LEQ];
       ASSUME_TAC (CONJUNCT2 (SPEC "x:zet" ONE_LEQ)) THEN
       SUB_ASSUM_TAC [1;2] THEN IMP_RES_TAC TRANSITIVITY_LEQ THEN
       ASM_REWRITE_TAC[]]);; 
                                                                   

%<******************PRE_MULT_THEOREMS**********************************>%  

let w44 = "!x y z.(ZET_REL x y) ==> ZET_REL (x PRE_MULT z) (y PRE_MULT z)";;

let thm44 = prove(
    w44,
    3 TIMES (CONV_TAC PROD_CONV THEN (2 TIMES GEN_TAC)) THEN
    REWRITE_TAC[ZET_REL;PRE_MULT] THEN
    REPEAT STRIP_TAC THEN
    ASSUM_LIST (\[th].ASSUME_TAC (MK_MULT [th;REFL "z1:num"])) THEN
    FILTER_ASSUM_LIST [2] (\[th].ASSUME_TAC (MK_MULT [SYM th;REFL "z2:num"])) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[RIGHT_ADD_DISTRIB]) THEN
    CONV_TAC (DIR_CONV [`faaa`,CM;`aaa`,CM]) THEN
    CONV_TAC (DIR_CONV [`fa`,LR;`faa`,RL;`faafa`,CP;`faa`,CP;`fa`,RL]) THEN
    CONV_TAC (DIR_CONV [`a`,LR;`aa`,RL;`aafa`,CP;`aa`,CP;`a`,RL]) THEN
    ASM_REWRITE_TAC[]);;

let w45 = "!x y z.(ZET_REL x y) ==> ZET_REL (z PRE_MULT x) (z PRE_MULT y)";;

let thm45 = prove(
    w45,
    3 TIMES (CONV_TAC PROD_CONV THEN (2 TIMES GEN_TAC)) THEN
    REWRITE_TAC[ZET_REL;PRE_MULT] THEN
    REPEAT STRIP_TAC THEN
    ASSUM_LIST (\[th].ASSUME_TAC (MK_MULT [REFL "z1:num";th])) THEN
    FILTER_ASSUM_LIST [2] (\[th].ASSUME_TAC (MK_MULT [REFL "z2:num";SYM th])) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[LEFT_ADD_DISTRIB]) THEN
    CONV_TAC (DIR_CONV [`faaa`,CM;`aaa`,CM]) THEN
    CONV_TAC (DIR_CONV [`fa`,LR;`faa`,RL;`faafa`,CP;`faa`,LR;`faaa`,CP;`fa`,RL]) THEN
    CONV_TAC (DIR_CONV [`a`,LR;`aa`,RL;`aafa`,CP;`aa`,LR;`aaa`,CP;`a`,RL]) THEN
    ASM_REWRITE_TAC[]);;


let w46 = "!x y z w.(ZET_REL x y) /\ (ZET_REL z w) ==>
                      ZET_REL (x PRE_MULT z) (y PRE_MULT w)";;

let thm46 = prove(
    w46,
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC (SPEC_ALL thm44) THEN
    IMP_RES_TAC (SPEC "y:num#num" (SPEC "z:num#num" (SPEC "w:num#num" thm45))) THEN
    SUB_ASSUM_TAC [2;5] THEN
    ASSUM_LIST (\[th1;th2].ASSUME_TAC (CONJ th2 th1)) THEN
    ASSUME_TAC ((BETA_RULE o (REWRITE_RULE[TRANSITIVITY])) thm3) THEN
    FILTER_ASSUM_LIST [1;2] (\[th1;th2].ASSUME_TAC (MATCH_MP th1 th2)) THEN
    ASM_REWRITE_TAC[]);;

let w47 = "?!h.PROJ_zet o (\z.(FST z) PRE_MULT (SND z)) = h o (PROJ_zet P PROJ_zet)";;

let thm47 = prove(
    w47,
    MATCH_MP_TAC FACTOR_THM THEN
    REWRITE_TAC[ONTO_SURJ_THM;thm_onto;o_DEF;P] THEN
    BETA_TAC THEN
    REWRITE_TAC[PAIR_EQ_THM;thm_univ;thm46]);;

let thm48 = 
    let th1 = (CONV_RULE (BINDER_CONV (SYM_CONV THENC FUN_EQ_CONV THENC PROD_CONV))) thm47 in
    let th2 = (CONV_RULE (BINDER_CONV PROD_CONV)) th1 in
    let th3 = REWRITE_RULE[o_DEF;P] th2 in
    let th4 = BETA_RULE th3 in   
    let th5 = REWRITE_RULE[PRE_MULT] th4 in
    let th6 = hd(CONJUNCTS CURRY_ISO) in
    let th7 = (CONV_RULE (BASE_CHANGE_CONV th6)) th5 in
    REWRITE_RULE[UNCURRY_DEF] th7;;

%<***********************DEFINITIONS****************************************>%   

let [MULT;MULT_UNIQUE] = new_unique_specification `MULT` [`infix`,`mult`] thm48;;  
                                                                                   

%<*************************DEFINITIONS********************************>%

let LESS = new_infix_definition(
   `LESS`,
    "less x y =(x plus een) leq y");;  

%<******************LESS_LEQQ_THEOREMS**********************************>%

let w49 = "!x y. (x less y) = ((x leq y) /\ ~(x = y))";;

let LESS_LEQ = prove_thm(
   `LESS_LEQ`,
    w49,
    REPEAT GEN_TAC 
    THEN REWRITE_TAC[LESS] THEN 
    EQ_TAC THEN 
    REPEAT STRIP_TAC THENL
     [ASSUME_TAC (CONJUNCT2 (SPEC "x:zet" ONE_LEQ)) THEN
      IMP_RES_TAC TRANSITIVITY_LEQ;
      REWRITE_RULE_ASSUM_TAC [2] [1] THEN
      ASSUME_TAC (CONJUNCT2 (SPEC "y:zet" ONE_LEQ)) THEN
      IMP_RES_TAC ANTI_SYM_LEQ THEN
      IMP_RES_TAC ONE_PROPER_LEQ;
      DISJ_CASES_TAC (SPEC "y:zet" (SPEC "x:zet" DISCRETE_ZET)) THEN
      ASM_REWRITE_TAC[] THEN
      IMP_RES_TAC ANTI_SYM_LEQ THEN
      RES_TAC]);;

let w50 = "!x.~(x less x)";;

let IRREFLEX_LESS = prove_thm(
   `IRREFLEX_LESS`,
    w50,
    REWRITE_TAC[LESS_LEQ]);;

let w51 = "!x y z.(x less y) /\ (y leq z) ==> (x less z)";;

let thm51 = prove(
    w51,
    REWRITE_TAC[LESS] THEN REPEAT STRIP_TAC THEN IMP_RES_TAC TRANSITIVITY_LEQ);;

let w52 = "!x y z.(x leq y) /\ (y less z) ==> (x less z)";;

let thm52 = prove(
    w52,
    REWRITE_TAC[LESS] THEN 
    REPEAT STRIP_TAC THEN 
    NEW_IMP_RES_TAC TRANSLATION_LEQ THEN
    FILTER_RULE_ASSUM_TAC [1] (SPEC "een") THEN
    IMP_RES_TAC TRANSITIVITY_LEQ);; 

let w53 = "!x y z.(x less y) /\ (y less z) ==> (x less z)";;  

let thm53 = prove(
    w53,
    REPEAT STRIP_TAC THEN 
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[LESS_LEQ]) THEN
    FILTER_STRIP_ASSUM_TAC [1] THEN 
    IMP_RES_TAC thm51);;

let TRANSITIVITY_CLAUSES = save_thm(
   `TRANSITIVITY_CLAUSES`,
    (LIST_CONJ [TRANSITIVITY_LEQ;thm51;thm52;thm53]));;   

let w54 = "!x y. (x less y) = ((REV y) less (REV x))";; 

let REV_LESS = prove_thm(
   `REV_LESS`,
    w54,
    REWRITE_TAC[LESS_LEQ] THEN
    REPEAT GEN_TAC THEN 
    CONV_TAC (LHS_CONV (once_rewrite_CONV [REV_LEQ])) THEN
    EQ_TAC THEN 
    REPEAT STRIP_TAC THEN 
    ASM_REWRITE_TAC[] THEN
    FILTER_RULE_ASSUM_TAC [1] (\th.REWRITE_RULE[REV2_ID] (AP_TERM "REV" (SYM th))) THEN
    RES_TAC);;  

let w55 = "!k x.(x leq k) \/ (k less x)";;  

let LESS_LEQ_CASES = prove_thm(
   `LESS_LEQ_CASES`,
    w55,
    REWRITE_TAC[LESS;DISCRETE_ZET]);; 


%<*********************MULT_THEOREMS**********************************>%

let w56 = "!x y.(INT x) mult (INT y) = INT (x * y)";;

let INT_MULT = prove_thm(
    `INT_MULT`,
     w56,
     REWRITE_TAC[INT;MULT;thm_univ;ZET_REL;MULT_CLAUSES;ADD_CLAUSES]);;  

let w57 = "(!x.x mult zero = zero) /\ (!x.zero mult x = zero)";;   

let ZERO_MULT = prove_thm(
    `ZERO_MULT`,
     w57, 
     CONJ_TAC THEN
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[ZERO;INT;MULT;thm_univ;ZET_REL;MULT_CLAUSES;ADD_CLAUSES]);;

let w58 = "(!x.x mult een = x) /\ (!x.een mult x = x)";;    

let ONE_MULT = prove_thm(
    `ONE_MULT`,
     w58, 
     CONJ_TAC THEN
     ZET_QUOTIENT_TAC THEN
     REWRITE_TAC[ONE;INT;MULT;thm_univ;ZET_REL;MULT_CLAUSES;ADD_CLAUSES]);;

let w59 = "!x y.(x mult y) = (y mult x)";; 

let MULT_COM = prove_thm(
    `MULT_COM`,
     w59, 
     (2 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[MULT;thm_univ;ZET_REL;MULT_CLAUSES;ADD_CLAUSES] THEN
     CONV_TAC (DIR_CONV [`fafafa`,CM;`fafaa`,CM;`faa`,CP]) THEN
     REWRITE_TAC[]);; 

let w60 = "!x y z.x mult (y plus z) = ((x mult y) plus (x mult z))";;  

let PLUS_LEFT_DISTRIB = prove_thm(
    `PLUS_LEFT_DISTRIB`,
     w60,
     (3 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[MULT;PLUS;thm_univ;ZET_REL;LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB] THEN
     CONV_TAC (DIR_CONV[`fafa`,LR;`fafaa`,RL;`fafaafa`,CP;`fafaa`,LR;`fafa`,RL]) THEN
     CONV_TAC (DIR_CONV[`faa`,LR;`faaa`,RL;`faaafa`,CP;`faaa`,LR;`faa`,RL]) THEN
     REWRITE_TAC[]);;

let w61 = "!x y z.(y plus z) mult x = ((y mult x) plus (z mult x))";;  

let PLUS_RIGHT_DISTRIB = prove_thm(
    `PLUS_RIGHT_DISTRIB`,
     w61,
     (3 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[MULT;PLUS;thm_univ;ZET_REL;LEFT_ADD_DISTRIB;RIGHT_ADD_DISTRIB] THEN
     CONV_TAC (DIR_CONV[`fafa`,LR;`fafaa`,RL;`fafaafa`,CP;`fafaa`,LR;`fafa`,RL]) THEN
     CONV_TAC (DIR_CONV[`faa`,LR;`faaa`,RL;`faaafa`,CP;`faaa`,LR;`faa`,RL]) THEN
     REWRITE_TAC[]);;

let w62 = "!x y.REV( x mult y) = ((REV x) mult y)";;   

let REV_MULT1 = prove_thm(
    `REV_MULT1`,
     w62, 
     (2 TIMES ZET_QUOTIENT_TAC) THEN
     REWRITE_TAC[MULT;REV;thm_univ;ZET_REL] THEN
     CONV_TAC (DIR_CONV [`fafaa`,CM;`fafa`,CP;`faaa`,CM;`faa`,CP]) THEN
     ASM_REWRITE_TAC[]);; 

let w63 = "!x y.REV( x mult y) = (x mult (REV y))";;   

let REV_MULT2 = prove_thm(
    `REV_MULT2`,
     w63, 
     REPEAT GEN_TAC THEN
     CONV_TAC (RAND_CONV (REWRITE_CONV MULT_COM)) THEN
     REWRITE_TAC[SYM(SPEC_ALL REV_MULT1)] THEN
     CONV_TAC (RAND_CONV(RAND_CONV (REWRITE_CONV MULT_COM))) THEN
     REWRITE_TAC[]);; 

let w64 = "!x y z.x mult (y mult z) = (x mult y) mult z";; 

let MULT_ASSOC = prove_thm(
   `MULT_ASSOC`,
    w64,
    ZET_INDUCT2_TAC "zero" THEN
    ASM_REWRITE_TAC[ZERO_MULT;MINUS;PLUS_RIGHT_DISTRIB;
                    SYM(SPEC_ALL REV_MULT1);ONE_MULT]);;


let w65 = "!x y.(zero leq x) /\ (zero leq y) ==> (zero leq (x mult y))";; 

let LEQ_MULT = prove_thm(
   `LEQ_MULT`,
    w65,
    REWRITE_TAC[LEQ;MINUS;REWRITE_RULE[] (SPEC "zero" FIX_REV);ZERO_PLUS;POS] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC "y' * y''" THEN
    ASM_REWRITE_TAC[INT_MULT]);;

let MK_mult [th1;th2] = MK_COMB ((AP_TERM "$mult" th1),th2);;  

let w66 = "!x y.(een leq x) /\ (een leq y) ==> ((x leq (x mult y)) /\
                                                (y leq (x mult y)))";;

let thm66 = prove(
    w66,
    REWRITE_TAC[LEQ;MINUS;POS] THEN
    REPEAT STRIP_TAC THEN 
    ASSUM_LIST (\[th1;th2].ASSUME_TAC (MK_mult [th2;th1])) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[PLUS_LEFT_DISTRIB;PLUS_RIGHT_DISTRIB; 
                                   SYM(SPEC_ALL REV_MULT1);SYM(SPEC_ALL REV_MULT2);
                                   INT_MULT;ONE_MULT]) THENL
     [REWRITE_RULE_ASSUM_TAC [1] [2] THEN
      FILTER_RULE_ASSUM_TAC [1] (\th.MK_PLUS [th;REFL "INT y''"]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE[SYM(SPEC_ALL PLUS_ASSOC);REV_PLUS_ZERO;
                                   ZERO_PLUS;INT_PLUS]) THEN
      EXISTS_TAC "(y' * y'') + y''" THEN
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC (REWRITE_RULE[REV_PLUS]) THEN
      FILTER_RULE_ASSUM_TAC [1] 
             (CONV_RULE (DIR_CONV [`fa`,lr;`faa`,rl;`faafa`,cp;`faa`,lr;`fa`,rl])) THEN
      FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[SYM(SPEC_ALL REV_PLUS)]) THEN 
      REWRITE_RULE_ASSUM_TAC [1] [3] THEN
      FILTER_RULE_ASSUM_TAC [1] (\th.MK_PLUS [th;REFL "INT y'"]) THEN
      RULE_ASSUM_TAC (REWRITE_RULE[SYM(SPEC_ALL PLUS_ASSOC);REV_PLUS_ZERO;
                                   ZERO_PLUS;INT_PLUS]) THEN
      EXISTS_TAC "(y' * y'') + y'" THEN
      ASM_REWRITE_TAC[]]);;  

let w67 = "!x.(x leq (REV een)) \/ (x = zero) \/ (een leq x)";;  

let thm67 = prove(
    w67,
    GEN_TAC THEN 
    DISJ_CASES_TAC 
      (REWRITE_RULE[ZERO_PLUS] (SPEC "x:zet" (SPEC "zero" DISCRETE_ZET))) THENL
       [DISJ_CASES_TAC 
       (REWRITE_RULE[REV_PLUS_ZERO] (SPEC "x:zet" (SPEC "REV een" DISCRETE_ZET))) THENL
         [ASM_REWRITE_TAC[];
          IMP_RES_TAC ANTI_SYM_LEQ  THEN
          SUB_ASSUM_TAC [1] THEN 
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]);; 

let w68 = "!x y.~(x = zero) /\ ~(y = zero) ==> ~(( x mult y) = zero)";; 

let thm68 = prove(
    w68,
    REPEAT STRIP_TAC THEN 
    DISJ_CASES_TAC (SPEC "x:zet" thm67) THEN
    DISJ_CASES_TAC (SPEC "y:zet" thm67) THEN
    RES_TAC THEN 
    REWRITE_RULE_ASSUM_TAC [1;2] [4;5] THENL
     [FILTER_RULE_ASSUM_TAC [1;2] (ONCE_REWRITE_RULE[REV_LEQ]);
      FILTER_RULE_ASSUM_TAC [2] (ONCE_REWRITE_RULE[REV_LEQ]);
      FILTER_RULE_ASSUM_TAC [1] (ONCE_REWRITE_RULE[REV_LEQ]);
      ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[REV2_ID]) THEN
    IMP_RES_TAC thm66 THEN
    SUB_ASSUM_TAC [1;8;10] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[SYM(SPEC_ALL REV_MULT1);
                                 SYM(SPEC_ALL REV_MULT2);
                                 REV2_ID]) THEN
    IMP_RES_TAC TRANSITIVITY_LEQ THEN
    IMP_RES_TAC ZERO_LEQ_ONE THEN
    SUB_ASSUM_TAC [2;8] THEN
    REWRITE_RULE_ASSUM_TAC [1] [2] THEN
    FILTER_RULE_ASSUM_TAC [1] (REWRITE_RULE[REWRITE_RULE[] (SPEC "zero" FIX_REV)]) THEN
    ASM_REWRITE_TAC[]);;

let w69 = "!x y.((x mult y) = zero) = ((x =zero) \/ (y =zero))";;

let MULT_EQ_ZERO = prove_thm(
   `MULT_EQ_ZER0`,
    w69,
    REPEAT STRIP_TAC THEN 
    EQ_TAC THEN 
    REPEAT STRIP_TAC THEN 
    ASM_REWRITE_TAC[ZERO_MULT] THEN
    ASM_CASES_TAC "x = zero" THEN 
    ASM_CASES_TAC "y = zero" THEN 
    ASM_REWRITE_TAC[] THEN
    IMP_RES_TAC thm68);;
                            
let w70 = "!x y.(zero less x) /\ (zero less y) ==> (zero less (x mult y))";;

let LESS_MULT = prove_thm(
   `LESS_MULT`,
    w70,
    REWRITE_TAC[LESS;ZERO_PLUS] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC thm66 THEN
    IMP_RES_TAC TRANSITIVITY_LEQ);;

%<***********************DEFINITIONS****************************************>%   

let MIN = new_definition(
   `MIN`,
    "MIN Q = @x.((Q x) /\ (!y.(Q y) ==> (x leq y)))");;

let MAX = new_definition(
   `MAX`,
    "MAX Q = @x.((Q x) /\ (!y.(Q y) ==> (y leq x)))");; 


%<*************************THEOREMS**********************************>%


let w71 = "!Q.!k l.(!x.(x leq k) ==> ~(Q x)) /\ (Q l) ==> 
           (?z.(Q z) /\ (!w.(Q w) ==> (z leq w)))";;  

let thm71 = prove(
    w71,
    REPEAT STRIP_TAC THEN 
    ASM_CASES_TAC "(?z.(Q z) /\ (!w.(Q w) ==> (z leq w)))" THEN
    ASM_REWRITE_TAC[] THEN
    FILTER_RULE_ASSUM_TAC [1] (CONV_RULE NOT_EXISTS_CONV) THEN
    SUBGOAL_THEN "!x y.(y leq x) ==> ~(Q y)" ASSUME_TAC THENL
    [ZET_INDUCT2_TAC "k:zet";ALL_TAC] THENL
      [RES_TAC;
       ASSUME_TAC (CONJUNCT1(SPEC "x:zet" ONE_LEQ)) THEN
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       RES_TAC;
       DISJ_CASES_TAC (SPEC "y:zet"(SPEC "x:zet" DISCRETE_ZET)) THENL
       [RES_TAC;ALL_TAC] THEN
       IMP_RES_TAC ANTI_SYM_LEQ THEN
       REWRITE_RULE_ASSUM_TAC [7] [1] THEN 
       SUB_ASSUM_TAC [7;9;10;11;12;13] THEN
       FILTER_RULE_ASSUM_TAC [4] (SPEC "x plus een") THEN
       REWRITE_RULE_ASSUM_TAC [4] [1] THEN
       FILTER_ASSUM_TAC [4] UNDISCH_TAC THEN
       REWRITE_TAC[] THEN
       REPEAT STRIP_TAC THEN
       DISJ_CASES_TAC (SPEC "w:zet"(SPEC "x:zet" DISCRETE_ZET)) THEN 
       RES_TAC THEN
       ASM_REWRITE_TAC[];
       FILTER_RULE_ASSUM_TAC [1] 
          (\th.REWRITE_RULE[REFLEX_LEQ] (SPEC "l:zet"(SPEC "l:zet" th))) THEN
       RES_TAC]);; 

let thm72 = 
    let th1 = REWRITE_RULE[EXISTS_DEF] thm71 in
    let th2 = BETA_RULE th1 in
    REWRITE_RULE[SYM(SPEC_ALL MIN)] th2;;

let MIN_EXISTS = save_thm(
   `MIN_EXISTS`,
    thm72);;

let w73 = "!Q.!k l.(!x.(k leq x) ==> ~(Q x)) /\ (Q l) ==> 
           (?z.(Q z) /\ (!w.(Q w) ==> (w leq z)))";;  

let thm73 = prove(
    w73,
    REPEAT STRIP_TAC THEN 
    ASM_CASES_TAC "(?z.(Q z) /\ (!w.(Q w) ==> (w leq z)))" THEN
    ASM_REWRITE_TAC[] THEN
    FILTER_RULE_ASSUM_TAC [1] (CONV_RULE NOT_EXISTS_CONV) THEN
    SUBGOAL_THEN "!x y.(x leq y) ==> ~(Q y)" ASSUME_TAC THENL
    [ZET_INDUCT2_TAC "k:zet";ALL_TAC] THENL
      [RES_TAC;
       DISJ_CASES_TAC (SPEC "y:zet"(SPEC "x minus een" DISCRETE_ZET)) THENL
          [ALL_TAC;
           RULE_ASSUM_TAC (ONCE_REWRITE_RULE[PLUS_COM]) THEN
           RULE_ASSUM_TAC (REWRITE_RULE[MINUS_PROP]) THEN
           RES_TAC] THEN
       IMP_RES_TAC ANTI_SYM_LEQ THEN
       REWRITE_RULE_ASSUM_TAC [7] [2] THEN 
       SUB_ASSUM_TAC [7;9;10;11;12;13] THEN
       FILTER_RULE_ASSUM_TAC [4] (SPEC "x minus een") THEN
       REWRITE_RULE_ASSUM_TAC [4] [1] THEN
       FILTER_ASSUM_TAC [4] UNDISCH_TAC THEN
       REWRITE_TAC[] THEN
       REPEAT STRIP_TAC THEN
       DISJ_CASES_TAC (SPEC "w:zet"(SPEC "x minus een" DISCRETE_ZET)) THEN 
       ASM_REWRITE_TAC[] THEN
       RULE_ASSUM_TAC (ONCE_REWRITE_RULE[PLUS_COM]) THEN
       RULE_ASSUM_TAC (REWRITE_RULE[MINUS_PROP]) THEN
       RES_TAC;
       ASSUME_TAC (CONJUNCT2(SPEC "x:zet" ONE_LEQ)) THEN
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       IMP_RES_TAC TRANSITIVITY_LEQ THEN
       RES_TAC;
       FILTER_RULE_ASSUM_TAC [1] 
          (\th.REWRITE_RULE[REFLEX_LEQ] (SPEC "l:zet"(SPEC "l:zet" th))) THEN
       RES_TAC]);; 

let thm74 = 
    let th1 = REWRITE_RULE[EXISTS_DEF] thm73 in
    let th2 = BETA_RULE th1 in
    REWRITE_RULE[SYM(SPEC_ALL MAX)] th2;;

let MAX_EXISTS = save_thm(
   `MAX_EXISTS`,
    thm74);;

%<********************EXTRA**EXTRA*****************************>%

let SIGMA = new_list_rec_definition(
   `SIGMA`,
    "(SIGMA [] = zero) /\ (SIGMA (CONS h tl) = (h plus (SIGMA tl)))");;  

let PI = new_list_rec_definition(
   `PI`,
    "(PI [] = een) /\ (PI (CONS h tl) = (h mult (PI tl)))");; 

let w75 = "!l1 l2.(SIGMA (APPEND l1 l2)) = ((SIGMA l1) plus (SIGMA l2))";; 

let SIGMA_APPEND = prove_thm(
   `SIGMA_APPEND`,
    w75,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[APPEND;SIGMA;ZERO_PLUS;PLUS_ASSOC]);;

let w76 = "!l1 l2.(PI (APPEND l1 l2)) = ((PI l1) mult (PI l2))";; 

let PI_APPEND = prove_thm(
   `PI_APPEND`,
    w76,
    LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[APPEND;PI;ONE_MULT;MULT_ASSOC]);;   
























