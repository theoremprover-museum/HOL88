%<
AUTHOR:	Ton Kalker

DATE:	13 september 1989

COMMENT: proves some basic theorems
         on functions on sets.

NOTE: some proofs modified for version 1.12.  No longer uses
      the auxiliary library tactics.

>%


% --------------------------------------------------------------------- %
% Load code from auxiliary library.                      [TFM 90.12.02]	%
% --------------------------------------------------------------------- %

% loadf (library_pathname() ^ `/auxiliary/tactics`);; %

  
%<
load_theory `pred_sets`;;
                            
autoload_defs_and_thms `pred_sets`;; 
>% 

%<
new_special_symbol `-->>`;;

new_special_symbol `>-->`;;   

new_special_symbol `<-->`;; 
>%  

let w = "!A B (f:*->*).(((A >-->B) f) \/ ((A -->> B) f)) ==> ((A --> B) f)";;  

let FUN_TY = prove_thm(
   `FUN_TY`,
    w,
    REPEAT STRIP_TAC THEN 
    RULE_ASSUM_TAC (REWRITE_RULE[FUN_ONTO;FUN_ONE_ONE]) THEN
    ASM_REWRITE_TAC[FUN_TY_DEF]);;

let w = "!A (B:*->bool).!f.((A --> B) f) = ((IMAGE f A) SUBSET B)";;

let FUN_TY_IMAGE =
    prove_thm
    (`FUN_TY_IMAGE`,
      w,
     REPEAT GEN_TAC THEN
     REWRITE_TAC[IMAGE;SUBSET;FUN_TY_DEF] THEN
     EQ_TAC THEN  
     REPEAT STRIP_TAC THENL
     [RES_TAC THEN ASM_REWRITE_TAC [];
      FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC "x:*" THEN
      ASM_REWRITE_TAC[]]);;

let w = "!A (B:*->bool).!f:*->*.((A -->> B) f) = ((IMAGE f A) = B)";;

let ONTO_IMAGE =
    prove_thm
    (`ONTO_IMAGE`,
      w,
      REPEAT GEN_TAC THEN 
      CONV_TAC (RAND_CONV FUN_EQ_CONV) THEN
      REWRITE_TAC [IMAGE;FUN_ONTO] THEN
      EQ_TAC THEN
      REPEAT STRIP_TAC THENL
      [REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
       [RES_TAC THEN ASM_REWRITE_TAC [];
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
       FIRST_ASSUM (\th g. REWRITE_TAC [SYM(SPEC_ALL th)] g) THEN
       EXISTS_TAC "x:*" THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC []]);;

let w= "!A:*->bool.!f g. (IMAGE g (IMAGE f A)) = IMAGE (g o f) A";; 

let IMAGE_COMP  =
    prove_thm(
    `IMAGE_COMP`,
     w, 
     CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
     REPEAT GEN_TAC THEN
     REWRITE_TAC [IMAGE;o_DEF] THEN
     BETA_TAC THEN
     EQ_TAC THEN
     REPEAT STRIP_TAC THENL
           [EXISTS_TAC "b':*" THEN 
            ASM_REWRITE_TAC[];
            EXISTS_TAC "f (b:*):*" THEN
            ASM_REWRITE_TAC[] THEN
            EXISTS_TAC "b:*" THEN
            ASM_REWRITE_TAC[]]);;  

let w1 = "!A:*->bool.(A --> A) I";;

let thm1 =
    prove
     (w1,
      REPEAT GEN_TAC THEN
      REWRITE_TAC[FUN_TY_DEF] THEN
      BETA_TAC THEN
      REWRITE_TAC[I_THM]);;

let w2 = "!A:*->bool.(A >--> A) I";;  

let thm2 =
    prove
     (w2,
      REPEAT GEN_TAC THEN
      REWRITE_TAC[FUN_ONE_ONE;thm1] THEN
      BETA_TAC THEN 
      REWRITE_TAC[I_THM] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[]);;  

let w3 = "!A:*->bool.(A -->> A) I";; 

let thm3 =
    prove
     (w3,
      REPEAT GEN_TAC THEN
      REWRITE_TAC[FUN_ONTO;thm1] THEN
      BETA_TAC THEN 
      REWRITE_TAC[I_THM] THEN
      REPEAT STRIP_TAC THEN 
      EXISTS_TAC "x:*" THEN
      ASM_REWRITE_TAC[]);;  
 
let w4 = "!A:*->bool.(A <--> A) I";; 

let thm4 =
    prove
     (w4,
      REPEAT GEN_TAC THEN
      REWRITE_TAC[FUN_ISO] THEN
      BETA_TAC THEN
      REWRITE_TAC[thm2;thm3]);;

let FUN_IDEN =
    save_thm
    (`FUN_IDEN`,
    GEN_ALL (LIST_CONJ (map SPEC_ALL [thm1;thm2;thm3;thm4])));;

let w1 = "!B.!f:*->*.((BOT --> B) f)";;  

let thm1 = 
      prove(
      w1,
      REWRITE_TAC[FUN_TY_DEF;BOT]);;   

let w2 = "!B.!f:*->*.((BOT >--> B) f)";;

let thm2 =
       prove(
       w2,
       REWRITE_TAC[BOT;FUN_ONE_ONE]);;  
                                                    

let w3 =  "!B.!f:*->*.((BOT -->> B)f) = (B = BOT)";;   

let thm3 = 
       prove(
       w3,
       REWRITE_TAC[BOT;FUN_ONTO] THEN
       GEN_TAC THEN
       CONV_TAC SYM_CONV THEN
       CONV_TAC (LHS_CONV (FUN_EQ_CONV THENC (REDEPTH_CONV BETA_CONV))) THEN
       REWRITE_TAC[]);; 

let w4 =  "!B.!f:*->*.((BOT <--> B)f) = (B = BOT)";;

let thm4 = 
       prove(
       w4,
       REPEAT GEN_TAC THEN
       REWRITE_TAC[FUN_ISO;thm2;thm3]);;

let BOTTOM_LEFT =
       save_thm(
       `BOTTOM_LEFT`,
       GEN_ALL (LIST_CONJ (map SPEC_ALL [thm1;thm2;thm3;thm4])));;

let w1 = "!A.!f:*->*.((A --> BOT) f) = (A = BOT)";;  

let thm1 = 
       prove(
       w1,
       REWRITE_TAC[BOT;FUN_TY_DEF] THEN
       GEN_TAC THEN
       CONV_TAC SYM_CONV THEN
       CONV_TAC (LHS_CONV (FUN_EQ_CONV THENC (REDEPTH_CONV BETA_CONV))) THEN
       REWRITE_TAC[]);; 

let w2 = "!A.!f:*->*.((A >--> BOT) f) = (A = BOT)";;  

let thm2 = 
       prove(
       w2,
       REWRITE_TAC[BOT;FUN_ONE_ONE] THEN 
       BETA_TAC THEN
       REPEAT GEN_TAC THEN
       CONV_TAC SYM_CONV THEN
       CONV_TAC (LHS_CONV (FUN_EQ_CONV THENC (REDEPTH_CONV BETA_CONV))) THEN
       REWRITE_TAC[] THEN 
       EQ_TAC THEN 
       STRIP_TAC THEN 
       REPEAT CONJ_TAC THEN 
       ASM_REWRITE_TAC[]);;

let w3 = "!A.!f:*->*.((A -->> BOT) f) = (A = BOT)";;  

let thm3 = 
       prove(
       w3,
       REWRITE_TAC[BOT;FUN_ONTO] THEN 
       BETA_TAC THEN
       REPEAT GEN_TAC THEN
       CONV_TAC SYM_CONV THEN
       CONV_TAC (LHS_CONV (FUN_EQ_CONV THENC (REDEPTH_CONV BETA_CONV))) THEN
       REWRITE_TAC[]);; 

let w4 = "!A.!f:*->*.((A <--> BOT) f) = (A = BOT)";;  

let thm4 = 
       prove(
       w4,
       REPEAT GEN_TAC THEN
       REWRITE_TAC[FUN_ISO;thm2;thm3]);;


let BOTTOM_RIGHT =
      save_thm(
       `BOTTOM_RIGHT`,
        GEN_ALL (LIST_CONJ (map SPEC_ALL [thm1;thm2;thm3;thm4])));; 

let w1 = "!A B (D:*->bool).!f g.((A --> B)f) /\ ((B --> D)g) ==>
                                 ((A --> D)(g o f))";;   

let thm1 = 
    prove
    (w1, 
     REPEAT GEN_TAC THEN 
     REWRITE_TAC[FUN_TY_DEF;o_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     RES_TAC THEN RES_TAC);;

let w2 = "!A B (D:*->bool).!f g.((A >--> B)f) /\ ((B >--> D)g) ==>
                                 ((A >--> D)(g o f))";;

let thm2 = 
    prove
    (w2, 
     REPEAT GEN_TAC THEN 
     REWRITE_TAC[FUN_ONE_ONE;o_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN
     RES_TAC THEN RES_TAC);;

let w3 = "!A B (D:*->bool).!f g.((A -->> B)f) /\ ((B -->> D)g) ==>
                                 ((A -->> D)(g o f))";;  

let thm3 = 
    prove
    (w3, 
     REPEAT GEN_TAC THEN 
     REWRITE_TAC[ONTO_IMAGE;SYM (SPEC_ALL IMAGE_COMP)] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[]);;


let w4 = "!A B (D:*->bool).!f g.((A <--> B)f) /\ ((B <--> D)g) ==>
                                 ((A <--> D)(g o f))";; 

let thm4 = 
    prove
    (w4, 
     REPEAT GEN_TAC THEN 
     REWRITE_TAC[FUN_ISO] THEN 
     BETA_TAC THEN
     REPEAT STRIP_TAC THEN 
     MAP_EVERY IMP_RES_TAC [thm2;thm3]);;

let FUN_COMP =
    save_thm
    (`FUN_COMP`,
    GEN_ALL (LIST_CONJ (map SPEC_ALL [thm1;thm2;thm3;thm4])));;  

let w = "!A.~(A = BOT) = (?x:*.A x)";;  

let NOT_BOT = 
    prove_thm(
   `NOT_BOT`,
    w,
    GEN_TAC THEN
    REWRITE_TAC[BOT] THEN
    BETA_TAC THEN 
    CONV_TAC ((ONCE_DEPTH_CONV FUN_EQ_CONV) THENC    
              (ONCE_DEPTH_CONV NOT_FORALL_CONV)) THEN
    REWRITE_TAC[]);;

let w =" !A (B:*->bool).!f g g'.((PINVERSE (A,B) f g) /\ (PINVERSE (B,A) g' f))
                                                    ==>
                               ((PINVERSE (A,B) f g') /\ (PINVERSE (B,A) g f))";;

let LR_INV =
    prove_thm(
    `LR_INV`,
     w,
     REWRITE_TAC[PINVERSE;FUN_TY_DEF;o_DEF] THEN
     BETA_TAC THEN
     REPEAT STRIP_TAC THEN 
     ASM_REWRITE_TAC[] THEN 
     RES_TAC THEN RES_TAC THENL
      [RES_TAC THEN
       RULE_ASSUM_TAC (SUBS [ASSUME "f(g'(f (x:*):*):*):* = f x"]) THEN
       IMP_RES_TAC EQ_SYM THEN IMP_RES_TAC EQ_TRANS;
       RULE_ASSUM_TAC (SUBS [ASSUME "f(g' (x:*):*):* = x"]) THEN
       SUBST1_TAC (ASSUME "g (x:*):* = g' x") THEN RES_TAC]);;


let w = "! A B (f:*->*).(~(A = BOT)) ==> (B --> A) (FINV A B f)";;


let FUN_INV_TY = 
    prove_thm(
    `FUN_INV_TY`,
     w,
     REPEAT GEN_TAC THEN 
     REWRITE_TAC[NOT_BOT;FUN_TY_DEF;FUN_INV] THEN
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     COND_CASES_TAC THENL
     [POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE);
      CONV_TAC SELECT_CONV THEN
      EXISTS_TAC "x:*" THEN FIRST_ASSUM ACCEPT_TAC]);;


let w = "!A B (f:*->*).(( ~(A = BOT)) /\ ((A >--> B) f))  ==> 
                       (PINVERSE (A,B) f (FINV A B f))";; 

let INJ_FINV =
    prove_thm(
    `INJ_FINV`,
     w, 
     REPEAT GEN_TAC THEN
     REWRITE_TAC [FUN_ONE_ONE;PINVERSE;FUN_TY_DEF;o_DEF] THEN
     BETA_TAC THEN
     REPEAT STRIP_TAC THENL   
      [RES_TAC;  
       IMP_RES_TAC (REWRITE_RULE[FUN_TY_DEF] FUN_INV_TY) THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC;
       REWRITE_TAC[FUN_INV] THEN
       FIRST_ASSUM MATCH_MP_TAC THEN
       REPEAT CONJ_TAC THENL
       [RES_TAC THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THENL
        [POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE);
         CONV_TAC SELECT_CONV THEN EXISTS_TAC "x:*" THEN
         FIRST_ASSUM ACCEPT_TAC];
        FIRST_ASSUM ACCEPT_TAC;
        AP_TERM_TAC THEN
        RES_TAC THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THENL
        [POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE) THEN
         CONV_TAC SYM_CONV THEN RES_TAC;
         POP_ASSUM (MP_TAC o SPEC "x:*" o CONV_RULE NOT_EXISTS_CONV) THEN
         ASM_REWRITE_TAC []]]]);;


let w = "!A B (f:*->*).(( ~(A = BOT)) /\ ((A -->> B) f))  ==>
                       (PINVERSE (B,A) (FINV A B f) f)";; 

let SURJ_FINV =
    prove_thm(
    `SURJ_FINV`,
     w,  
     REPEAT GEN_TAC THEN
     REWRITE_TAC [FUN_ONTO;PINVERSE;FUN_TY_DEF;o_DEF] THEN
     BETA_TAC THEN
     REPEAT STRIP_TAC THENL 
      [IMP_RES_TAC (REWRITE_RULE[FUN_TY_DEF] FUN_INV_TY) THEN
       FIRST_ASSUM MATCH_ACCEPT_TAC;
       RES_TAC;
       REWRITE_TAC[FUN_INV] THEN
       RES_THEN ASSUME_TAC THEN
       ASM_REWRITE_TAC[] THEN
       CONV_TAC SYM_CONV THEN
       POP_ASSUM (STRIP_ASSUME_TAC o SELECT_RULE)]);;

let w = "!A B (f:*->*) g.(((A --> B) f) /\ ((B --> A) g) /\ (PINVERSE (A,B) f g)) ==>
                 (((A >--> B) f) /\ ((B -->> A) g))";;  

let INJ_SURJ_PINVERSE = prove_thm(
   `INJ_SURJ_PINVERSE`,
    w,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC[FUN_TY_DEF;FUN_ONE_ONE;FUN_ONTO;PINVERSE;o_DEF] THEN     
    BETA_TAC THEN 
    REPEAT STRIP_TAC THEN 
    RES_TAC THENL
     [EVERY_ASSUM (\th g. SUBST1_TAC (SYM th) g ? ALL_TAC g) THEN REFL_TAC;
      EXISTS_TAC "f (x:*):*" THEN 
      ASM_REWRITE_TAC[]]);; 

let w = "!A (B:*->bool) f g.((A --> B) f) /\ ((B --> A) g) /\ (INVERSE (A,B) f g) ==>
                           (((A <--> B) f) /\ ((B <--> A) g))";;

let ISO_INVERSE =
    prove_thm(
    `ISO_INVERSE`,
     w, 
     REWRITE_TAC[INVERSE;FUN_ISO] THEN
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC INJ_SURJ_PINVERSE);;


let w = "!A (B:*->bool).!f.((A <--> B)f) ==> ((B <--> A) (FINV A B f))";;  

% Proof modified for new IMP_RES_TAC			[TFM 90.04.29]  %

let ISO_FINV =
    prove_thm(
   `ISO_FINV`,
    w, 
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [FUN_ISO] THEN
    ASM_CASES_TAC "(A:*->bool) = BOT" THEN
    ASM_REWRITE_TAC[BOTTOM_LEFT;BOTTOM_RIGHT] THEN
    ASM_CASES_TAC "(B:*->bool) = BOT" THEN
    ASM_REWRITE_TAC[BOTTOM_LEFT;BOTTOM_RIGHT] THEN
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC FUN_TY THEN
    REPEAT_GTCL IMP_RES_THEN (ASSUME_TAC o SPEC_ALL) FUN_INV_TY THEN
    MAP_EVERY IMP_RES_TAC [SURJ_FINV;INJ_FINV;INJ_SURJ_PINVERSE]);;

