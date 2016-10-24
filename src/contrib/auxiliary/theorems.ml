new_theory `auxiliary`;;

% Load certain definitions from bool.th					%

let ONTO_DEF = definition `bool` `ONTO_DEF`;;
let ONE_ONE_DEF = definition `bool` `ONE_ONE_DEF`;;


%<*************DEFINITIONS*********************************>%

let ISO = 
    new_definition
    (`ISO`,
     "ISO (f:*->**) = (ONE_ONE f) /\ (ONTO f)");;  

let INV=
    new_definition
    (`INV`,
     "INV (f:*->**) = \x:**.@y:*.x = (f y)");;  


%<*******************THEOREMS******************************>% 
         
let w = 
"!f.(ONTO (f:*->**)) ==> (!g h:**->***.(!x:*.(g(f x) = h(f x))) ==> (g = h))";;

let ONTO_PROPERTY = prove_thm(
        `ONTO_PROPERTY`,
         w, 
         PURE_ONCE_REWRITE_TAC [ONTO_DEF] THEN
         REPEAT STRIP_TAC THEN
         CONV_TAC FUN_EQ_CONV THEN 
         GEN_TAC THEN
         FIRST_ASSUM (\th g. STRIP_ASSUME_TAC (SPEC "x:**" th) g) THEN
         ASM_REWRITE_TAC[]);;

% The following is built-in: called PAIR_EQ	[TFM 91.01.29]		%

% let w = "!x1 x2:*.!y1 y2:**.(x1,y1 = x2, y2) = ((x1 = x2) /\ (y1 = y2))";; %

% let PAIR_EQ_THM = prove_thm(
     `PAIR_EQ_THM`,
      w, 
      REPEAT GEN_TAC THEN
      EQ_TAC THEN
      STRIP_TAC THENL
         [ASSUM_LIST (\asl.(MAP_EVERY ASSUME_TAC)
             [REWRITE_RULE [] (AP_TERM "FST:*#**->*" (hd asl));
              REWRITE_RULE [] (AP_TERM "SND:*#**->**" (hd asl))])
               THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]);;
%

let w = "ONTO (f:*->**) = (!x.f((INV f) x) = x)";;  

let RIGHT_INV = prove_thm(
   `RIGHT_INV`,
    w,
    PURE_ONCE_REWRITE_TAC[INV;ONTO_DEF] THEN
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    EQ_TAC THEN 
    REPEAT STRIP_TAC THENL
    [CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC;
     EXISTS_TAC "@x:*. (y:**) = f x" THEN
     CONV_TAC SYM_CONV THEN 
     FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let w = "ONE_ONE (f:*->**) = !x.((INV f) (f x)) = x";;

let LEFT_INV = prove_thm(
   `LEFT_INV`,
    w, 
    PURE_ONCE_REWRITE_TAC[ONE_ONE_DEF;INV] THEN
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN
     CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN
     EXISTS_TAC "x:*" THEN REFL_TAC;
     FIRST_ASSUM (\th g. ONCE_REWRITE_TAC [SYM (SPEC "x:*" th)] g) THEN
     FIRST_ASSUM SUBST1_TAC THEN REFL_TAC]);;

let w = "!f:*->**.!g:**->*.(!x.f(g x) = x) ==> ((ONTO f) /\ (ONE_ONE g))";;  

let ID_INJ_SURJ =
    prove_thm(
    `ID_INJ_SURJ`,
     w,
     PURE_ONCE_REWRITE_TAC[ONTO_DEF;ONE_ONE_DEF] THEN 
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC "(g:**->*) y" THEN ASM_REWRITE_TAC [];
      FIRST_ASSUM (\th g. ONCE_REWRITE_TAC [SYM (SPEC "x:**" th)] g) THEN
      FIRST_ASSUM SUBST1_TAC THEN REFL_TAC]);;


let w = "!f:*->**.!g:**->*.((!x.f(g x) = x) /\ (!x.g(f x) = x)) ==> 
                           ((ISO f) /\ (ISO g))";; 

let ID_ISO =
    prove_thm(
    `ID_ISO`,
     w,
     PURE_ONCE_REWRITE_TAC[ISO] THEN 
     REPEAT STRIP_TAC THEN 
     IMP_RES_TAC ID_INJ_SURJ);;

let w = "!f:*->**.!g:**->*.((!x.f(g x) = x) /\ (!x.g(f x) = x)) ==>   
                           ((INV f = g) /\ (INV g = f))";;

let INV_ISO =
   prove_thm(
   `INV_ISO`,
    w,
    REPEAT STRIP_TAC THEN 
    CONV_TAC FUN_EQ_CONV THEN
    GEN_TAC THENL
    [FIRST_ASSUM (\th g. SUBST1_TAC (SYM (SPEC "x:**" th)) g) THEN
     FIRST_ASSUM (\th g. SUBST1_TAC (SPEC "(g:**->*) x" th) g);
     FIRST_ASSUM (\th g. SUBST1_TAC (SYM (SPEC "x:*" th)) g) THEN
     FIRST_ASSUM (\th g. SUBST1_TAC (SPEC "(f:*->**) x" th) g)] THEN
    IMP_RES_TAC ID_INJ_SURJ THEN
    IMP_RES_TAC LEFT_INV THEN
    IMP_RES_TAC RIGHT_INV THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC);;

let w = "!f:*->**.!P.(ONTO f) ==> ((!x:**.P x) = (!y:*.P (f y)))";; 

let BASE_CHANGE_SURJ_FORALL = prove_thm(
      `BASE_CHANGE_SURJ_FORALL`,
       w,
       REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
       [FIRST_ASSUM MATCH_ACCEPT_TAC;
        IMP_RES_THEN (STRIP_ASSUME_TAC o SPEC "x:**") ONTO_DEF THEN
         ASM_REWRITE_TAC []]);;

let w = "!f:*->**.!P.(ISO f) ==> ((!x:**.P x) = (!y:*.P (f y)))";; 

% --------------------------------------------------------------------- %
% Proof rewritten for new IMP_RES_TAC			[TFM 90.04.29]	%
% --------------------------------------------------------------------- %

let BASE_CHANGE_ISO_FORALL = prove_thm(
      `BASE_CHANGE_ISO_FORALL`,
       w, 
       PURE_ONCE_REWRITE_TAC[ISO] THEN 
       REPEAT STRIP_TAC THEN 
       IMP_RES_TAC BASE_CHANGE_SURJ_FORALL THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC);;  

let w = "!f:*->**.!P.(ONTO f) ==> ((?x:**.P x) = (?y:*.P (f y)))";; 

let BASE_CHANGE_ONTO_EXISTS = prove_thm(
      `BASE_CHANGE_ONTO_EXISTS`,
       w,
       REPEAT STRIP_TAC THEN
       EQ_TAC THEN
       REPEAT STRIP_TAC THEN
       RULE_ASSUM_TAC (REWRITE_RULE[RIGHT_INV]) THENL
        [EXISTS_TAC "INV (f:*->**) x";
         EXISTS_TAC "(f:*->**) y"] THEN
       ASM_REWRITE_TAC[]);; 

let w = "!f:*->**.!P.(ISO f) ==> ((?x:**.P x) = (?y:*.P (f y)))";;  

let BASE_CHANGE_ISO_EXISTS = prove_thm(
      `BASE_CHANGE_ISO_EXISTS`,
       w,
       REWRITE_TAC[ISO] THEN
       REPEAT STRIP_TAC THEN
       IMP_RES_TAC BASE_CHANGE_ONTO_EXISTS THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC);; 

let w = "!f:*->**.!P.(ISO f) ==> ((?!x:**.P x) = (?!y:*.P (f y)))";;  

let BASE_CHANGE_EXISTS_UNIQUE = prove_thm(
  `BASE_CHANGE_EXISTS_UNIQUE`,
   w,  
   PURE_REWRITE_TAC [ISO;ONE_ONE_DEF;ONTO_DEF] THEN
   CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
    [let th = ASSUME "!y:**. ?x:*. y = f x" in
     STRIP_THM_THEN (ASSUME_TAC o SYM) (SPEC "x:**" th) THEN
     EXISTS_TAC "x':*" THEN ASM_REWRITE_TAC[];
     FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC;
     EXISTS_TAC "(f:*->**) y" THEN FIRST_ASSUM ACCEPT_TAC;
     let th = ASSUME "!y:**. ?x:*. y = f x" in
     STRIP_THM_THEN SUBST_ALL_TAC (SPEC "x:**" th) THEN
     STRIP_THM_THEN SUBST_ALL_TAC (SPEC "x':**" th) THEN
     AP_TERM_TAC THEN RES_TAC]);;

let w = "(!x:*1#*2.P x) = (!x1 x2.P (x1,x2))";; 

let PRODUCT_FORALL_THM = prove_thm(
      `PRODUCT_FORALL_THM`,
       w,
       EQ_TAC THEN REPEAT STRIP_TAC THENL
        [FIRST_ASSUM MATCH_ACCEPT_TAC;
         SUBST1_TAC (SYM(ISPEC "x:*1#*2" PAIR)) THEN
         FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let w = "(?x:*1#*2.P x) = (?x1 x2.P (x1,x2))";; 

let PRODUCT_EXISTS_THM = prove_thm(
      `PRODUCT_EXISTS_THM`,
       w,
       EQ_TAC THEN 
       REPEAT STRIP_TAC THENL
        [EXISTS_TAC "(FST:*1#*2->*1) x" THEN
         EXISTS_TAC "(SND:*1#*2->*2) x";
         EXISTS_TAC "(x1:*1,x2:*2)"] THEN
       ASM_REWRITE_TAC[]);;

%<PROD_CONV needed; conversions loaded uncompiled>%

loadf `conversions`;; 

let w = "!f:*#**->***.(UNCURRY(CURRY f) = f)";; 

let THM_UC = prove(w,
           GEN_TAC THEN
           CONV_TAC (FUN_EQ_CONV THENC (REDEPTH_CONV BETA_CONV)) THEN
           CONV_TAC PROD_CONV THEN
           REWRITE_TAC[CURRY_DEF;UNCURRY_DEF]);;

let w = "!f:*->**->***.(CURRY(UNCURRY f) = f)";;

let THM_CU = prove(w, 
           GEN_TAC THEN 
           (CONV_TAC FUN_EQ_CONV) THEN 
           (CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)) THEN
           REWRITE_TAC[UNCURRY_DEF;CURRY_DEF]);;   

let CURRY_THM =
         save_thm(
         `CURRY_THM`,
          (LIST_CONJ ([THM_UC;THM_CU])));;

let CURRY_ISO =
         save_thm(
         `CURRY_ISO`,
          MATCH_MP ID_ISO CURRY_THM);; 

%<The following theorems are useful in conjunction
  with MATCH_MP>%

let w0 = "!Q.(!x:*.((Q x) = (?y:**.x = f y))) ==> !y.Q (f y)";;

let w1 = "!Q.(!x:*.((Q x) = (?y:**.(f y) = x))) ==> !y.Q (f y)";;

let DEF_THM1 = prove_thm(
   `DEF_THM1`,
    w0,
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC "y:**" THEN
    REWRITE_TAC[]);;

let DEF_THM2 = prove_thm(
   `DEF_THM2`,
    w1,
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC "y:**" THEN
    REWRITE_TAC[]);;  

%<Theorem for use with new_specification: removes
  free variables>%   

let SPEC_THM = prove_thm(
   `SPEC_THM`,
    "(!y:*1.?z:*2.Q y z) = (?f.!y.Q y (f y))",
    EQ_TAC THEN 
    REPEAT STRIP_TAC THENL
    [EXISTS_TAC "\y:*1.@z:*2.Q y z" THEN
     BETA_TAC THEN
     RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE[EXISTS_DEF]) THEN
     ASM_REWRITE_TAC[];
     EXISTS_TAC "f (y:*1):*2" THEN
     ASM_REWRITE_TAC[]]);;


