% ===================================================================== %
% FILE:         greatest.ml                                             %
% DESCRIPTION:  theory about the greatest of a list of natural numbers  %
%               and inequalities involving it.                          %
% AUTHOR:       Catia M. Angelo                                         %
%               IMEC VZW                                                %
%               Kapeldreef, 75                                          %
%               B3001 - Leuven - Belgium                                %
%               e-mail: catia@imec.be                                   %
% DATE:         June 4th, 1993.                                         %
% ===================================================================== %
% HOL88 - Version 2.0                                                   %
% Loaded libraries: unwind; reduce; more_arithmetic; auxiliary.         %
% ===================================================================== %

%-----------------------------------------------------------------------%
% Note: This theory has not been polished or optimized.                 %
%-----------------------------------------------------------------------%

new_theory `greatest`;;

loadf `compat`;;

map load_library [`more_arithmetic`];;

% ===================================================================== %
% DEFINITIONS                                                           %
% ===================================================================== %

let GRT = new_list_rec_definition (`GRT`,
   "((GRT [] ref) = ref) /\
    ((GRT ((CONS hd tl):(num)list) ref) =
     (GRT tl ((hd < ref) => ref | hd)))");;

let GREATEST = new_definition (`GREATEST`,
"! (l:(num)list). GREATEST l = GRT l 0");;

let GEQKL = new_list_rec_definition (`GEQKL`,
"((GEQKL [] k) = T) /\
 ((GEQKL (CONS h t) k) = ((k >= h) /\ (GEQKL t k)))");;

let GKL = new_list_rec_definition (`GKL`,
"((GKL [] k) = T) /\
 ((GKL (CONS h t) k) = ((k > h) /\ (GKL t k)))");;

% ===================================================================== %
% AUXILIARY TACTICS                                                     %
% ===================================================================== %

%---------------------------------------------------------------%
% These versions of IMP_RES_THEN and IMP_RES_TAC only add to    %
% the assumption list theorems that do not have implications.   %
%---------------------------------------------------------------%

let OLD_IMP_RES_THEN' tac thm =
OLD_IMP_RES_THEN (\th. if (is_imp (snd (dest_thm th)))
                      then ALL_TAC
                      else (tac th)) thm;;

let OLD_IMP_RES_TAC' thm = OLD_IMP_RES_THEN' ASSUME_TAC thm;;

let REWRITE_ALL_TAC thmList =
POP_ASSUM_LIST (\asslist.
        let newasslist = map (\th. REWRITE_RULE thmList th) asslist in
        MAP_EVERY ASSUME_TAC newasslist) THEN
REWRITE_TAC thmList;;

let LHS_CONV = RATOR_CONV o RAND_CONV;;

let RHS_CONV = RAND_CONV;;

%---------------------------------------------------------------%
% UNDISCH_ALL_TAC:                                              %
%       This tactic does the opposite of the rule UNDISCH_ALL.  %
% It should be used only in goals without implications.         %
%                                                               %
%                       A,t1,...,tn |- t                        %
%               =================================               %
%               A |- t1 ==> ... ==> tn ==> t                    %
%---------------------------------------------------------------%

letrec new_goal (asl, t) =
        if asl = [] then (asl,t)
                    else (new_goal (tl asl, mk_imp (hd asl, t)));;

let UNDISCH_ALL_TAC (asl, t) =
                    ( [(new_goal (asl,t))], UNDISCH_ALL o hd  );;

% ===================================================================== %
% THEOREMS                                                              %
% ===================================================================== %

%-----------------------------------------------------------------------%
% AUXILIARY THEOREMS ABOUT ARITHMETIC                                   %
%-----------------------------------------------------------------------%

let GREATER_IMP_GREATER_0 = prove_thm (`GREATER_IMP_GREATER_0`,
"!n m. (n > m) ==> (n > 0)",
REPEAT STRIP_TAC THEN
POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER] th)) THEN
ASSUME_TAC (SPEC "m:num" ZERO_LESS_EQ) THEN
IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
ASM_REWRITE_TAC[GREATER]);;

let GREATER_EQ_TRANS = prove_thm (`GREATER_EQ_TRANS`,
"!m n p. n >= m /\ p >= n ==> p >= m",
  ACCEPT_TAC (REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL GREATER_EQ))]
                           LESS_EQ_TRANS));;

let GREATER_EQ_REFL = prove_thm (`GREATER_EQ_REFL`,
"!m. m >= m",
 ACCEPT_TAC (REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL GREATER_EQ))]
LESS_EQ_REFL));;

let LESS_OR_NOT_LESS = save_thm (`LESS_OR_NOT_LESS`,
REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL NOT_LESS))] LESS_CASES);;

let NOT_LESS' = save_thm (`NOT_LESS'`,
REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL GREATER_EQ))]
             NOT_LESS);;

let NOT_LESS'' = save_thm (`NOT_LESS''`,
REWRITE_RULE [GREATER_EQ; LESS_OR_EQ] NOT_LESS');;

let NOT_LESS''' = save_thm (`NOT_LESS'''`,
REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL LESS_OR_EQ))] NOT_LESS'');;

let GREATER_NOT_ZERO' = prove_thm (`GREATER_NOT_ZERO'`,
"!x. (0 < x) = (~(x = 0))",
GEN_TAC THEN
EQ_TAC THENL
[
 REWRITE_TAC[GREATER_NOT_ZERO]
;
 MP_TAC (SPEC "x:num" num_CASES) THEN
 ASM_REWRITE_TAC[] THEN
 STRIP_TAC THEN
 ASM_REWRITE_TAC[LESS_0]
]);;

let LESS_IMP_LESS_EQ_SUB = prove_thm (`LESS_IMP_LESS_EQ_SUB`,
"! h x k. (h < x) ==> ((h - k) <= (x - k))",
REPEAT STRIP_TAC THEN
DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "k <= h" BOOL_CASES_AX)) THENL
[ % k <= h %
 IMP_RES_TAC SUB_LESS_BOTH_SIDES THEN
 IMP_RES_TAC LESS_IMP_LESS_OR_EQ
; %~(k <= h) %
 POP_ASSUM (\th. ASSUME_TAC
   (REWRITE_RULE [GEN_ALL(SYM(SPEC_ALL LESS_IS_NOT_LESS_OR_EQ))] th)) THEN
 IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
 IMP_RES_TAC (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL SUB_EQ_0)))) THEN
 ASM_REWRITE_TAC[ZERO_LESS_EQ]
]);;

%-----------------------------------------------------------------------%
% GREATER_EQ_ZERO = |- !n. n >= 0                                       %
%-----------------------------------------------------------------------%
let GREATER_EQ_ZERO = prove_thm (`GREATER_EQ_ZERO`,
"!n. n >= 0",
REWRITE_TAC[GREATER_EQ; ZERO_LESS_EQ]);;

% --------------------------------------------------------------------- %

let GREATEST_N_ZERO = prove_thm (`GREATEST_N_ZERO`,
"! n. GREATEST[n;0] = n",
GEN_TAC THEN
REWRITE_TAC[GREATEST;GRT;NOT_LESS_0] THEN
MP_TAC (SPEC_ALL (REWRITE_RULE[LESS_OR_EQ] ZERO_LESS_EQ)) THEN
DISJ_CASES_TAC (SPEC "0 < n" BOOL_CASES_AX) THEN
ASM_REWRITE_TAC[] );;

let GRT_REF = prove_thm (`GRT_REF`,
"! l ref. (k >= (GRT l ref)) = ((k >= ref) /\ (k >= (GRT l 0)))",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GRT; GREATER_EQ; ZERO_LESS_EQ]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[GRT; NOT_LESS_0] THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "ref:num"] LESS_CASES) THENL
 [
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM (\th.  ASSUME_TAC (SPEC "ref:num" th)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
  [
   REPEAT STRIP_TAC THENL
   [
    ASM_REWRITE_TAC[]
   ;
    POP_ASSUM (\th. ALL_TAC) THEN
    POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER_EQ] th)) THEN
    IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
    IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
    ASM_REWRITE_TAC[GREATER_EQ]
   ;
    ASM_REWRITE_TAC[]
   ]
  ;
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[]
  ]
 ;
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ASSUME_TAC (REWRITE_RULE
                [GEN_ALL (SYM (SPEC_ALL NOT_LESS))] th)) THEN
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM (\th.  ASSUME_TAC (SPEC "h:num" th)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
  [
   REPEAT STRIP_TAC THENL
   [
    REWRITE_TAC[GREATER_EQ] THEN
    POP_ASSUM (\th. ALL_TAC) THEN
    POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER_EQ] th)) THEN
    MP_TAC (SPECL ["ref:num"; "h:num"; "k:num"] LESS_EQ_TRANS) THEN
    ASM_REWRITE_TAC[]
   ;
    ASM_REWRITE_TAC[]
   ;
    ASM_REWRITE_TAC[]
   ]
  ;
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[]
  ]
 ]
]);;

let GRT_REF' = prove_thm (`GRT_REF'`,
"! l ref. (k > (GRT l ref)) = ((k > ref) /\ (k > (GRT l 0)))",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GRT] THEN
 GEN_TAC THEN
 EQ_TAC THENL
 [
  STRIP_TAC THEN
  IMP_RES_TAC GREATER_IMP_GREATER_0 THEN
  ASM_REWRITE_TAC[]
 ;
  STRIP_TAC THEN
  ASM_REWRITE_TAC[]
 ]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[GRT; NOT_LESS_0] THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "ref:num"] LESS_CASES) THENL
 [
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM (\th.  ASSUME_TAC (SPEC "ref:num" th)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
  [ % h < ref %
   REPEAT STRIP_TAC THENL
   [
    ASM_REWRITE_TAC[]
   ;
    POP_ASSUM (\th. ALL_TAC) THEN
    POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER] th)) THEN
    IMP_RES_TAC LESS_TRANS THEN
    ASM_REWRITE_TAC[GREATER]
   ;
    ASM_REWRITE_TAC[]
   ]
  ;
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[]
  ]
 ; % ref <= h %
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ASSUME_TAC (REWRITE_RULE
                [GEN_ALL (SYM (SPEC_ALL NOT_LESS))] th)) THEN
  POP_ASSUM (\th. (ASSUME_TAC th) THEN ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM (\th.  ASSUME_TAC (SPEC "h:num" th)) THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
  [
   REPEAT STRIP_TAC THENL
   [
    REWRITE_TAC[GREATER] THEN
    POP_ASSUM (\th. ALL_TAC) THEN
    POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER] th)) THEN
    IMP_RES_TAC LESS_EQ_LESS_TRANS
   ;
    ASM_REWRITE_TAC[]
   ;
    ASM_REWRITE_TAC[]
   ]
  ;
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[]
  ]
 ]
]);;

let GREATEST_GEQKL = prove_thm (`GREATEST_GEQKL`,
"! l k. (k >= GREATEST l) = (GEQKL l k)",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GREATEST; GRT; GEQKL; GREATER_EQ; ZERO_LESS_EQ]
;
 REPEAT GEN_TAC THEN
 POP_ASSUM (\th. MP_TAC th) THEN
 REWRITE_TAC[GREATEST; GRT; GEQKL; NOT_LESS_0] THEN
 DISCH_THEN (\th. ASSUME_TAC (SPEC_ALL th)) THEN
 ONCE_REWRITE_TAC[GRT_REF] THEN
 ASM_REWRITE_TAC[]
]);;

let GREATEST_GKL = prove_thm (`GREATEST_GKL`,
"! l k. (~(l = [])) ==> ((k > GREATEST l) = (GKL l k))",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[(GEN_ALL(NOT_EQ_SYM(SPEC_ALL NOT_NIL_CONS)))] THEN
 DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "(l:(num)list) = []" BOOL_CASES_AX)) THENL
 [
  ASM_REWRITE_TAC[GREATEST; GRT; GKL; NOT_LESS_0]
 ;
  POP_ASSUM_LIST (\thmlist. MAP_EVERY
        (\th. ASSUME_TAC (SPEC_ALL th)) thmlist) THEN
  POP_ASSUM (\th. MP_TAC th) THEN
  ASM_REWRITE_TAC[GREATEST; GRT; GKL; NOT_LESS_0] THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[GRT_REF'] THEN
  ASM_REWRITE_TAC[]
 ]
]);;

%------------------------------------------------------------------%
% #GREATEST_GKL_CONS;;                                             %
% |- !k hd tl. k > (GREATEST(CONS hd tl)) = GKL(CONS hd tl)k       %
%------------------------------------------------------------------%

let GREATEST_GKL_CONS = save_thm (`GREATEST_GKL_CONS`,
GEN_ALL (REWRITE_RULE [INST_TYPE [(":num", ":*")] NOT_CONS_NIL]
(SPECL ["(CONS (hd:num) (tl:(num)list))"; "k:num"]
GREATEST_GKL)));;

let GEQKL_CONS = prove_thm (`GEQKL_CONS`,
"! tl hd k. (GEQKL [hd] k) /\ (GEQKL tl k) = (GEQKL (CONS hd tl) k)",
LIST_INDUCT_TAC THEN REWRITE_TAC[GEQKL]);;

let GEQKL_APP = prove_thm (`GEQKL_APP`,
"! l1 l2 k.
   (GEQKL l1 k) /\ (GEQKL l2 k) = (GEQKL (APPEND l1 l2) k)",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GEQKL; APPEND]
;
 REWRITE_TAC[GEQKL; APPEND] THEN
 ASM_REWRITE_TAC[GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))]
]);;

let GREATEST_APP = prove_thm (`GREATEST_APP`,
"!l1 l2 k. k >= (GREATEST l1) /\ k >= (GREATEST l2) =
 k >= (GREATEST(APPEND l1 l2))",
 ACCEPT_TAC (REWRITE_RULE [(GEN_ALL (SYM (SPEC_ALL GREATEST_GEQKL)))]
                          GEQKL_APP));;

let GEQKL_APP_SYM = prove_thm (`GEQKL_APP_SYM`,
"! l1 l2 k. (GEQKL (APPEND l1 l2) k) = (GEQKL (APPEND l2 l1) k)",
REWRITE_TAC[GEN_ALL (SYM (SPEC_ALL GEQKL_APP))] THEN
REPEAT GEN_TAC THEN
CONV_TAC (ONCE_DEPTH_CONV (LHS_CONV (REWRITE_CONV CONJ_SYM))) THEN
REWRITE_TAC[]);;

let GREATEST_APP_SYM = prove_thm (`GREATEST_APP_SYM`,
"!l1 l2 k.
  k >= (GREATEST(APPEND l1 l2)) = k >= (GREATEST(APPEND l2 l1))",
  ACCEPT_TAC (REWRITE_RULE [(GEN_ALL (SYM (SPEC_ALL GREATEST_GEQKL)))]
                           GEQKL_APP_SYM));;

let GEQKL_TRANS = prove_thm (`GEQKL_TRANS`,
"! l k1 k2. ((GEQKL l k1) /\ (k2 >= k1)) ==> (GEQKL l k2)",
REWRITE_TAC[(GEN_ALL(SYM (SPEC_ALL GREATEST_GEQKL)))] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC GREATER_EQ_TRANS);;

let GEQKL_EVERY = prove_thm (`GEQKL_EVERY`,
"!l k. GEQKL l k = EVERY (\el. k >= el) l",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GEQKL; EVERY_DEF]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[GEQKL; EVERY_DEF] THEN
 BETA_TAC THEN
 ASM_REWRITE_TAC[]
]);;

let GREATEST_EVERY = prove_thm (`GREATEST_EVERY`,
"!l k. k >= (GREATEST l) = EVERY(\el. k >= el)l",
  ACCEPT_TAC (REWRITE_RULE [(GEN_ALL (SYM (SPEC_ALL GREATEST_GEQKL)))]
                           GEQKL_EVERY));;

let EVERY_GREATEST = save_thm (`EVERY_GREATEST`,
GEN_ALL (REWRITE_RULE [GREATER_EQ_REFL]
(SPECL ["l:(num)list"; "GREATEST l"] GREATEST_EVERY)));;

let GREATEST_GRT = prove_thm (`GREATEST_GRT`,
"! hd tl. GREATEST (CONS hd tl) = GRT tl hd",
REPEAT GEN_TAC THEN
REWRITE_TAC[GREATEST; GRT; NOT_LESS_0]);;

let REF_LESS_EQ_GRT = prove_thm (`REF_LESS_EQ_GRT`,
"! l ref. ref <= (GRT l ref)",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GRT; LESS_EQ_REFL]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[GRT] THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "ref:num"] LESS_OR_NOT_LESS) THENL
 [
  ASM_REWRITE_TAC[]
 ;
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM (\th. MP_TAC th) THEN
  POP_ASSUM (\th. ASSUME_TAC (SPEC "h:num" th)) THEN
  DISCH_THEN (\th. ASSUME_TAC (REWRITE_RULE [NOT_LESS] th)) THEN
  IMP_RES_TAC LESS_EQ_TRANS
 ]
]);;

let GRT_APPEND = prove_thm (`GRT_APPEND`,
"!l1 l2 k.
 k >= (GRT l1 0) /\ (k >= GRT l2 0) =
 k >= GRT (APPEND l1 l2) 0",
REWRITE_TAC[GEN_ALL (SYM (SPEC_ALL GREATEST))] THEN
ACCEPT_TAC GREATEST_APP);;

let GRT_APP_SYM = prove_thm (`GRT_APP_SYM`,
"!l1 l2 k.
    k >= (GRT (APPEND l1 l2) 0) = k >= (GRT (APPEND l2 l1) 0)",
REWRITE_TAC[GEN_ALL (SYM (SPEC_ALL GREATEST))] THEN
ACCEPT_TAC GREATEST_APP_SYM);;

let GRT_EVERY = prove_thm (`GRT_EVERY`,
"!l k. k >= (GRT l 0) = EVERY(\el. k >= el)l",
REWRITE_TAC[GEN_ALL (SYM (SPEC_ALL GREATEST))] THEN
ACCEPT_TAC GREATEST_EVERY);;

let GRT_CONS = save_thm (`GRT_CONS`,
REWRITE_RULE[GREATEST] GREATEST_GRT);;

let GRT_REF_IS_GRT_0_OR_REF = prove_thm (`GRT_REF_IS_GRT_0_OR_REF`,
"!l h. GRT l h = ((h < (GRT l 0)) => (GRT l 0) | h)",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GRT] THEN
 GEN_TAC THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "0"] LESS_OR_NOT_LESS) THENL
 [
  REWRITE_TAC[NOT_LESS_0]
 ;
  ASM_REWRITE_TAC[]
 ]
;
 REWRITE_TAC[GRT_CONS; GRT] THEN
 REPEAT GEN_TAC THEN
 POP_ASSUM (\th. ASSUME_TAC (SPEC "h:num" th) THEN
                 ASSUME_TAC (SPEC "h':num" th)) THEN
 ASM_REWRITE_TAC[] THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "GRT l 0"] LESS_OR_NOT_LESS) THENL
 [ % h < (GRT l 0) %
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC (SPECL ["h:num"; "h':num"] LESS_OR_NOT_LESS) THENL
  [ % h < (GRT l 0) ; h < h' %
   ASM_REWRITE_TAC[]
  ; % h < (GRT l 0) ; ~(h < h') %
   ASM_REWRITE_TAC[] THEN
   POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE[NOT_LESS'''] th)) THEN
   IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
   ASM_REWRITE_TAC[]
  ]
 ; % ~(h < (GRT l 0)) %
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC (SPECL ["h:num"; "h':num"] LESS_OR_NOT_LESS) THENL
  [ % ~(h < (GRT l 0)) ; h < h' %
   ASM_REWRITE_TAC[] THEN
   IMP_RES_THEN (\th. ASSUME_TAC th)
        (GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL NOT_LESS)))) THEN
   OLD_IMP_RES_TAC' (SPECL ["(GRT l 0)"; "h:num"; "h':num"]
        (hd (CONJUNCTS LESS_EQ_LESS_TRANS))) THEN
   IMP_RES_THEN (\th. REWRITE_TAC[th]) NOT_LESS_AND_GREATER
  ; % ~(h < (GRT l 0)) ; ~(h < h') %
   ASM_REWRITE_TAC[] THEN
   POP_ASSUM (\th. DISJ_CASES_TAC (REWRITE_RULE [NOT_LESS''] th)) THENL
   [ % h' < h %
     ASM_REWRITE_TAC[]
   ; % h' = h %
     IMP_RES_THEN (\th. REWRITE_TAC[th]) NOT_LESS_EQ THEN
     ASM_REWRITE_TAC[]
   ]
  ]
 ]
]);;

let GRT_REF_IS_GREATEST_OR_REF = prove_thm (`GRT_REF_IS_GREATEST_OR_REF`,
"!l h. GRT l h = ((h < (GREATEST l) => (GREATEST l) | h))",
REWRITE_TAC[GREATEST] THEN
ACCEPT_TAC GRT_REF_IS_GRT_0_OR_REF);;

let GEQKL_GREATEST = prove_thm (`GEQKL_GREATEST`,
"!l. GEQKL l (GREATEST l)",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[GEQKL]
;
 REWRITE_TAC[GREATEST; GRT; NOT_LESS_0] THEN
 ONCE_REWRITE_TAC[GRT_REF_IS_GRT_0_OR_REF] THEN
 GEN_TAC THEN
 DISJ_CASES_TAC (SPECL ["h:num"; "(GRT l 0)"] LESS_OR_NOT_LESS) THENL
 [
  ASM_REWRITE_TAC[] THEN
  REWRITE_ALL_TAC[GEQKL; GREATEST; GRT; NOT_LESS_0] THEN
  REWRITE_TAC[GREATER_EQ] THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  ASM_REWRITE_TAC[]
 ;
  ASM_REWRITE_TAC[] THEN
  REWRITE_ALL_TAC[GEQKL; GREATEST; GRT; NOT_LESS_0; GREATER_EQ_REFL;
                  NOT_LESS'] THEN
  IMP_RES_TAC GEQKL_TRANS
 ]
]);;

let GEQKL_GRT = prove_thm (`GEQKL_GRT`,
"!l. GEQKL l (GRT l 0)",
REWRITE_TAC[GEN_ALL(SYM (SPEC_ALL GREATEST))] THEN
ACCEPT_TAC GEQKL_GREATEST);;

let GRT_0_LESS_EQ_GRT_REF = prove_thm (`GRT_0_LESS_EQ_GRT_REF`,
"! l ref. (GRT l 0) <= (GRT l ref)",
REPEAT GEN_TAC THEN
CONV_TAC (RHS_CONV (REWRITE_CONV GRT_REF_IS_GRT_0_OR_REF)) THEN
DISJ_CASES_TAC (SPECL ["ref:num"; "(GRT l 0)"] LESS_OR_NOT_LESS) THENL
[
 ASM_REWRITE_TAC[LESS_EQ_REFL]
;
 ASM_REWRITE_TAC[GEN_ALL(SYM(SPEC_ALL NOT_LESS))]
]);;

let GEQKL_GRT' = save_thm (`GEQKL_GRT'`,
GEN_ALL (REWRITE_RULE [GRT_0_LESS_EQ_GRT_REF]
(REWRITE_RULE [GEQKL_GRT; GREATER_EQ]
             (SPECL ["l:(num)list"; "(GRT l 0)"; "(GRT l ref)"]
                    GEQKL_TRANS))));;

let GRT_TRANS = prove_thm (`GRT_TRANS`,
"! l k1 k2. ((GRT l k1) <= k2) ==> ((GRT l k2) = k2)",
ONCE_REWRITE_TAC[GRT_REF_IS_GRT_0_OR_REF] THEN
REPEAT GEN_TAC THEN
DISJ_CASES_TAC (SPECL ["k1:num"; "(GRT l 0)"] LESS_OR_NOT_LESS) THENL
[
 ASM_REWRITE_TAC[] THEN
 REPEAT STRIP_TAC THEN
 ASM_REWRITE_TAC[(GEN_ALL(SYM (SPEC_ALL NOT_LESS_EQ_LESS)))]
;
 ASM_REWRITE_TAC[] THEN
 POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [NOT_LESS] th)) THEN
 DISCH_TAC THEN
 OLD_IMP_RES_TAC' LESS_EQ_TRANS THEN
 POP_ASSUM (\th. REWRITE_TAC[
        REWRITE_RULE [GEN_ALL(SYM (SPEC_ALL NOT_LESS))] th])
]);;

let GREATEST_TRANS = save_thm (`GREATEST_TRANS`,
REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL GREATEST))]
(SPECL ["l:(num)list"; "0:num"; "k:num"] GRT_TRANS));;

let GREATEST_CONS = prove_thm (`GREATEST_CONS`,
"! h t. (GREATEST(CONS h t)) = (GREATEST [h;GREATEST t])",
REWRITE_TAC[GREATEST_GRT] THEN
ONCE_REWRITE_TAC[GRT_REF_IS_GRT_0_OR_REF] THEN
REWRITE_TAC[GRT; NOT_LESS_0; GEN_ALL(SYM (SPEC_ALL GREATEST))]);;

let GREATEST_OF_ONE = prove_thm (`GREATEST_OF_ONE`,
"! k. GREATEST [k] = k",
REWRITE_TAC[GREATEST; GRT; NOT_LESS_0]);;

let GREATEST_OF_K_AND_0 = prove_thm (`GREATEST_OF_K_AND_0`,
"! k. GREATEST [k; 0] = k",
GEN_TAC THEN
REWRITE_TAC[GREATEST; GRT; NOT_LESS_0] THEN
DISJ_CASES_TAC (REWRITE_RULE [] (SPEC "0 < (k:num)" BOOL_CASES_AX)) THENL
[
 ASM_REWRITE_TAC[]
;
 ASM_REWRITE_TAC[] THEN
 POP_ASSUM (\th. ASSUME_TAC (REWRITE_RULE [GREATER_NOT_ZERO'] th)) THEN
 ASM_REWRITE_TAC[]
]);;

let GREATEST_OF_0_AND_K = prove_thm (`GREATEST_OF_0_AND_K`,
"! k. GREATEST [0; k] = k",
GEN_TAC THEN
REWRITE_TAC[GREATEST; GRT; NOT_LESS_0]);;

let PLUS_DISTRIB_GREATEST = prove_thm (`PLUS_DISTRIB_GREATEST`,
"! l k. (~(l = [])) ==>
        ((GREATEST l) + k = (GREATEST (MAP (\el. el + k) l)))",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[(GEN_ALL(NOT_EQ_SYM(SPEC_ALL NOT_NIL_CONS)))] THEN
 DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "(l:(num)list) = []" BOOL_CASES_AX)) THENL
 [
  ASM_REWRITE_TAC[MAP] THEN
  BETA_TAC THEN
  REWRITE_TAC[GREATEST; GRT; NOT_LESS_0]
 ;
  POP_ASSUM_LIST (\thmlist. MAP_EVERY
        (\th. ASSUME_TAC (SPEC_ALL th)) thmlist) THEN
  POP_ASSUM (\th. MP_TAC th) THEN
  ASM_REWRITE_TAC[MAP; GREATEST; GRT; NOT_LESS_0] THEN
  DISCH_THEN (\th. ASSUME_TAC (SYM th)) THEN
  BETA_TAC THEN
  ONCE_REWRITE_TAC[GRT_REF_IS_GRT_0_OR_REF] THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "(h:num) < (GRT l 0)" BOOL_CASES_AX)) THEN
                ONCE_REWRITE_TAC[ADD_SYM] THEN
                ASM_REWRITE_TAC[ADD_MONO_LESS]
 ]
]);;

%-----------------------------------------------------------------------%
% #PLUS_DISTRIB_GREATEST_CONS;;                                         %
% |- !hd tl k.                                                          %
%    (GREATEST(CONS hd tl)) + k = GREATEST(MAP(\el. el + k)(CONS hd tl))%
%-----------------------------------------------------------------------%

let PLUS_DISTRIB_GREATEST_CONS = save_thm (`PLUS_DISTRIB_GREATEST_CONS`,
GEN_ALL (REWRITE_RULE [INST_TYPE [(":num", ":*")] NOT_CONS_NIL]
(SPECL ["(CONS (hd:num) (tl:(num)list))"; "k:num"]
PLUS_DISTRIB_GREATEST)));;

let SUB_DISTRIB_GREATEST = prove_thm (`SUB_DISTRIB_GREATEST`,
"! l k. (~(l = [])) ==>
        ((GREATEST l) - k = (GREATEST (MAP (\el. el - k) l)))",
LIST_INDUCT_TAC THENL
[
 REWRITE_TAC[]
;
 REPEAT GEN_TAC THEN
 REWRITE_TAC[(GEN_ALL(NOT_EQ_SYM(SPEC_ALL NOT_NIL_CONS)))] THEN
 DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "(l:(num)list) = []" BOOL_CASES_AX)) THENL
 [
  ASM_REWRITE_TAC[MAP] THEN
  BETA_TAC THEN
  REWRITE_TAC[GREATEST; GRT; NOT_LESS_0]
 ;
  POP_ASSUM_LIST (\thmlist. MAP_EVERY
        (\th. ASSUME_TAC (SPEC_ALL th)) thmlist) THEN
  POP_ASSUM (\th. MP_TAC th) THEN
  ASM_REWRITE_TAC[MAP; GREATEST; GRT; NOT_LESS_0] THEN
  DISCH_THEN (\th. ASSUME_TAC (SYM th)) THEN
  BETA_TAC THEN
  ONCE_REWRITE_TAC[GRT_REF_IS_GRT_0_OR_REF] THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC (REWRITE_RULE []
        (SPEC "(h:num) < (GRT l 0)" BOOL_CASES_AX)) THENL
        [ % h < (GRT l 0) %
         DISJ_CASES_TAC (REWRITE_RULE []
                (SPEC "(h - k) < ((GRT l 0) - k)" BOOL_CASES_AX)) THENL
         [ % (h - k) < ((GRT l 0) - k) %
          ASM_REWRITE_TAC[]
         ; % ~((h - k) < ((GRT l 0) - k)) %
          ASM_REWRITE_TAC[] THEN
          IMP_RES_TAC LESS_IMP_LESS_EQ_SUB THEN
          POP_ASSUM (\th. MP_TAC (REWRITE_RULE[LESS_OR_EQ]
                (SPEC "k:num" th))) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN (\th. REWRITE_TAC[th])
         ]
        ; % ~(h < (GRT l 0)) %
         DISJ_CASES_TAC (REWRITE_RULE []
                (SPEC "(h - k) < ((GRT l 0) - k)" BOOL_CASES_AX)) THENL
         [ % (h - k) < ((GRT l 0) - k) %
          UNDISCH_ALL_TAC THEN
          REWRITE_TAC[NOT_LESS; LESS_OR_EQ] THEN
          DISJ_CASES_TAC (REWRITE_RULE []
                (SPEC "(GRT l 0) = h" BOOL_CASES_AX)) THENL
          [
           ASM_REWRITE_TAC[LESS_REFL]
          ;
           ASM_REWRITE_TAC[] THEN
           REPEAT DISCH_TAC THEN
           IMP_RES_TAC LESS_IMP_LESS_EQ_SUB THEN
           POP_ASSUM (\th. ASSUME_TAC
                (REWRITE_RULE [GEN_ALL(SYM(SPEC_ALL GREATER_EQ))]
                (SPEC "k:num" th))) THEN
           MP_TAC (SPECL ["(h - k)"; "((GRT l 0) - k)"]
                  GREATER_EQ_ANTISYM) THEN
           ASM_REWRITE_TAC[]
          ]
         ; % ~((h - k) < ((GRT l 0) - k)) %
          ASM_REWRITE_TAC[]
         ]
        ]
 ]
]);;

%------------------------------------------------------------------------%
% #SUB_DISTRIB_GREATEST_CONS;;                                           %
% |- !hd tl k.                                                           %
%    (GREATEST(CONS hd tl)) - k = GREATEST(MAP(\el. el - k)(CONS hd tl)) %
%------------------------------------------------------------------------%

let SUB_DISTRIB_GREATEST_CONS = save_thm (`SUB_DISTRIB_GREATEST_CONS`,
GEN_ALL (REWRITE_RULE [INST_TYPE [(":num", ":*")] NOT_CONS_NIL]
(SPECL ["(CONS (hd:num) (tl:(num)list))"; "k:num"]
SUB_DISTRIB_GREATEST)));;

let GREATEST_OF_AB = prove_thm (`GREATEST_OF_AB`,
"! a b. GREATEST[a;b] >= a /\ GREATEST[a;b] >= b",
REWRITE_TAC[GREATEST; GRT; NOT_LESS_0] THEN
REPEAT GEN_TAC THEN
DISJ_CASES_TAC (SPECL ["b:num"; "a:num"] LESS_CASES) THENL
[
 ASM_REWRITE_TAC[GREATER_EQ_REFL] THEN
 IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
 ASM_REWRITE_TAC[GREATER_EQ]
;
 POP_ASSUM (\th. ASSUME_TAC
           (REWRITE_RULE [GEN_ALL(SYM(SPEC_ALL NOT_LESS))] th)) THEN
 ASM_REWRITE_TAC[GREATER_EQ_REFL] THEN
 REWRITE_TAC[GREATER_EQ] THEN
 POP_ASSUM (\th. ACCEPT_TAC (REWRITE_RULE [NOT_LESS] th))
]);;

% ===================================================================== %
% TACTICS                                                               %
% ===================================================================== %

%-----------------------------------------------------------------------%
% FLAT_GREATEREQ_GREATEST_TAC: tactic                                   %
%-----------------------------------------------------------------------%
%       A ?-  x >= (GREATEST[GREATEST[ch1;ch2];GREATEST[ch3;ch4]])      %
% ====================================================================  %
%       A ?- (x >= ch1 /\ x >= ch2) /\ x >= ch3 /\ x >= ch4             %
%-----------------------------------------------------------------------%

let FLAT_GREATEREQ_GREATEST_THMS =
[GREATEST_GEQKL; GEQKL; GREATER_EQ_ZERO;
 GREATEST_GKL; GKL];;

let FLAT_GREATEREQ_GREATEST_TAC =
        REWRITE_TAC FLAT_GREATEREQ_GREATEST_THMS THEN
        BETA_TAC;;

%-----------------------------------------------------------------------%
% FLAT_GREATER_GREATEST_TAC: tactic                                     %
%-----------------------------------------------------------------------%
%       A ?-  x > (GREATEST[GREATEST[ch1;ch2];GREATEST[ch3;ch4]])       %
% ====================================================================  %
%       A ?- (x > ch1 /\ x > ch2) /\ x > ch3 /\ x > ch4                 %
%-----------------------------------------------------------------------%

let FLAT_GREATER_GREATEST_THMS =
[GREATEST_GKL_CONS; GKL; PLUS_DISTRIB_GREATEST_CONS;
SUB_DISTRIB_GREATEST_CONS; MAP; GREATEST_OF_K_AND_0; GREATEST_OF_0_AND_K];;

let FLAT_GREATER_GREATEST_TAC =
        REWRITE_TAC FLAT_GREATER_GREATEST_THMS THEN
        BETA_TAC;;

%-----------------------------------------------------------------------%
% EVERY_GREATEST_TAC: tactic                                            %
%-----------------------------------------------------------------------%
%  A ?- GREATEST[ch1; ch2; ch3; ch4] >= GREATEST[GREATEST[ch1; ch2];    %
%                                                GREATEST[ch3; ch4]]    %
% EVERY_GREATEST_TAC solves the goal by first flattening the right      %
% hand side and them rewriting the goal with the theorem "every_thm"    %
% generated from the left hand side:                                    %
% every_thm =                                                           %
% |- (GREATEST[ch1;ch2;ch3;ch4]) >= ch1 /\                              %
%    (GREATEST[ch1;ch2;ch3;ch4]) >= ch2 /\                              %
%    (GREATEST[ch1;ch2;ch3;ch4]) >= ch3 /\                              %
%    (GREATEST[ch1;ch2;ch3;ch4]) >= ch4                                 %
%-----------------------------------------------------------------------%

let EVERY_GREATEST_TAC:tactic (asl, w) =
let term = snd (dest_comb (fst (dest_comb w))) in
let (const, list) = (dest_comb term) in
let every_thm = (BETA_RULE (REWRITE_RULE [EVERY_DEF]
          (SPEC list EVERY_GREATEST))) in
let (string,_) = dest_const const in
if (string = `GREATEST`)
        then (REWRITE_TAC
        [GREATEST_GEQKL; GEQKL; GREATEST_GKL; GKL;
         every_thm; GREATER_EQ_ZERO] (asl, w))
        else ALL_TAC (asl, w);;

% ===================================================================== %

close_theory();;

