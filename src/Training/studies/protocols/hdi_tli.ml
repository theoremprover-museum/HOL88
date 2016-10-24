
%----------------------------------------------------------------------------%
% HDI TLI THEORY     1 August 1989                                           %
% Modified for HOL12 20/iii/91                                               %
%----------------------------------------------------------------------------%

new_theory`hdi_tli`;;

new_parent`myarith`;;
let SUB_PLUS=theorem`myarith``SUB_PLUS`;;

loadf`mytactics`;;

%----------------------------------------------------------------------------%
% DEFINITIONS                                                                %
%----------------------------------------------------------------------------%

let TLo=
new_definition(
  `TLo`,
  "TLo (l:* list) = ( (~(NULL l)) => TL l | [] )" );;

let TLI=
new_prim_rec_definition(
  `TLI`,
  "(TLI 0 (l:* list) = l) /\
   (TLI (SUC n) l = TLo (TLI n l) ) ");;

let HDI=
new_definition(
  `HDI`,
  "HDI (n:num) (l:* list) = HD( TLI n l)");;


%----------------------------------------------------------------------------%
%  HDI TLI lemmas   %
%----------------------------------------------------------------------------%

let LENGTH_TL =
prove_thm(
 `LENGTH_TL`,
 "!l:* list. ~NULL l ==> (LENGTH(TL l) = ((LENGTH l) - 1))",
  LIST_INDUCT_TAC THENL
  [ ASM_REWRITE_TAC[NULL] ;
    ASM_REWRITE_TAC[TL;LENGTH;SYM(SPEC_ALL PRE_SUB1);PRE]
  ] );;

let NULL_LENGTH_0 =
prove_thm(
  `NULL_LENGTH_0`,
  "!l:* list. (NULL l) ==> ((LENGTH l) = 0)",
  LIST_INDUCT_TAC THENL
  [ REWRITE_TAC[NULL;LENGTH] ;
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC NULL ] );;


let APPEND_NIL = 
prove_thm(
 `APPEND_NIL`,
 "!l:* list. APPEND l [] = l",
 LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND] );;

let TLI_NIL = 
prove_thm(
 `TLI_NIL`,
 "!n:num. TLI n ([]:* list) = []",
  INDUCT_TAC THEN ASM_REWRITE_TAC [TLI;TLo;NULL] );;

let HDI_TLI_1 = 
prove_thm(
  `HDI_TLI_1`,
  "!x:num. !l:* list.
   ~(NULL(TLI x l)) 
   ==> 
    ((APPEND [HDI x l] (TLI (x+1) l)) = (TLI x l))" , 
  INDUCT_TAC THENL
  [ REWRITE_TAC[SYM(SPEC_ALL ADD1);TLI;HDI;TLo;APPEND] THEN
    REPEAT STRIP_TAC THEN  IMP_RES_TAC CONS THEN
    ASM_REWRITE_TAC[] ;

    GEN_TAC THEN
    ASM_CASES_TAC "~NULL(TLI x (l:* list))" THEN
    ASM_REWRITE_TAC[SYM(SPEC_ALL ADD1);TLI;HDI;TLo;APPEND;NULL] THEN
    REPEAT STRIP_TAC THEN IMP_RES_TAC CONS THEN
    ASM_REWRITE_TAC[] ] );;


let HDI_TLI_2 =
prove_thm(
  `HDI_TLI_2`,
  "!x y:num. !l:* list. (TLI x (TLI y l)) = (TLI (x+y) l) ",
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[TLI;ADD_CLAUSES] );;

let HDI_TLI_3 =
prove_thm(
  `HDI_TLI_3`,
  "!x:num. !l:* list.  LENGTH(TLI x l) = (LENGTH(l) - x)",
  INDUCT_TAC THENL
  [ REWRITE_TAC [TLI;SUB_0] ;
    GEN_TAC THEN
    ASM_REWRITE_TAC [TLI;TLo] THEN
    ASM_CASES_TAC "NULL(TLI x (l:* list))" THENL
    [ IMP_RES_TAC NULL_LENGTH_0 THEN
      ASSUM_REWRITE_TAC SPEC_ALL 3 SPEC_ALL 1 THEN
      POP_ASSUM (ASSUME_TAC o SYM) THEN
      ASM_REWRITE_TAC[LENGTH;ADD1;SUB_PLUS;SUB_0] ;

      IMP_RES_TAC LENGTH_TL THEN
      ASM_REWRITE_TAC[ADD1;SUB_PLUS] ] ] );;


close_theory();;

quit();;

