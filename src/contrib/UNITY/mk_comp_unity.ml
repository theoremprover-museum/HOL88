% -*- Emacs Mode: fundamental -*- %


%-----------------------------------------------------------------------------%
%
   File:         mk_comp_unity.ml

   Description:  This file proves the unity compositionality theorems and
                 corrollaries valid.

   Authors:      (c) Copyright by Flemming Andersen
   Date:         December 1. 1989
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
autoload_defs_and_thms `ensures`;;
autoload_defs_and_thms `gen_induct`;;
autoload_defs_and_thms `leadsto`;;
%

system `/bin/rm comp_unity.th`;;

new_theory`comp_unity`;;

%-----------------------------------------------------------------------------%
%
  Theorems
%
%-----------------------------------------------------------------------------%

%
   Prove:
   !p q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) ==> (p UNLESS q) FPr /\ (p UNLESS q) GPr
%
let COMP_UNLESS_thm1_lemma_1 = TAC_PROOF
  (([],
   "!(p:*->bool) q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) ==> (p UNLESS q) FPr /\ (p UNLESS q) GPr"),
   REPEAT GEN_TAC THEN
   SPEC_TAC ("GPr:(*->*)list","GPr:(*->*)list") THEN
   SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS;APPEND]
     ;
      REWRITE_TAC [APPEND] THEN
      REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC
        ;
         RES_TAC]]);;

%
   Prove:
     !p q FPr GPr.
     (p UNLESS q) FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)
%
let COMP_UNLESS_thm1_lemma_2 = TAC_PROOF
  (([],
   "!(p:*->bool) q FPr GPr.
     (p UNLESS q) FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)"),
   REPEAT GEN_TAC THEN
   SPEC_TAC ("GPr:(*->*)list","GPr:(*->*)list") THEN
   SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS;APPEND]
     ;
      REWRITE_TAC [APPEND] THEN
      REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC
        ]]);;

%
   Prove:
     !p q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) FPr /\ (p UNLESS q) GPr
%
let COMP_UNLESS_thm1 = prove_thm
  (`COMP_UNLESS_thm1`,
   "!(p:*->bool) q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) FPr /\ (p UNLESS q) GPr",
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                       (SPEC_ALL COMP_UNLESS_thm1_lemma_1)
                       (SPEC_ALL COMP_UNLESS_thm1_lemma_2)));;



%
   Prove:
   !p q FPr GPr.
    (p ENSURES q) (APPEND FPr GPr) ==> (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr
%
let COMP_ENSURES_thm1_lemma_1 = TAC_PROOF
  (([],
   "!(p:*->bool) q FPr GPr.
    (p ENSURES q) (APPEND FPr GPr) ==> (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr"),
   REPEAT GEN_TAC THEN
   SPEC_TAC ("GPr:(*->*)list","GPr:(*->*)list") THEN
   SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND]
     ;
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND] THEN
      REPEAT STRIP_TAC THENL
        [
         DISJ1_TAC THEN
         ASM_REWRITE_TAC [] THEN
         ASM_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL COMP_UNLESS_thm1))]
        ;
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) UNLESS q)(APPEND FPr GPr)";
            "((p:*->bool) EXIST_TRANSITION q)(APPEND FPr GPr)"]
            AND_INTRO_THM)) THEN
         UNDISCH_TAC "((p:*->bool) UNLESS  q)(APPEND FPr GPr) /\
                       (p EXIST_TRANSITION q)(APPEND FPr GPr)" THEN
         REWRITE_TAC [SPECL ["p:*->bool";"q:*->bool";
                             "APPEND (FPr:(*->*)list) GPr"]
                             (GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
         DISCH_TAC THEN
         RES_TAC THENL
           [
            UNDISCH_TAC "((p:*->bool) ENSURES q)FPr" THEN
            REWRITE_TAC [ENSURES] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ;
            UNDISCH_TAC "((p:*->bool) ENSURES q)GPr" THEN
            REWRITE_TAC [ENSURES] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]]]);;


%
   Prove:
    !p q FPr GPr.
    (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
    (p ENSURES q) GPr /\ (p UNLESS q) FPr ==> (p ENSURES q) (APPEND FPr GPr)
%
let COMP_ENSURES_thm1_lemma_2 = TAC_PROOF
  (([],
   "!(p:*->bool) q FPr GPr.
    (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
    (p ENSURES q) GPr /\ (p UNLESS q) FPr ==> (p ENSURES q) (APPEND FPr GPr)"),
   REPEAT GEN_TAC THEN
   SPEC_TAC ("GPr:(*->*)list","GPr:(*->*)list") THEN
   SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND]
     ;
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC [COMP_UNLESS_thm1]
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC [COMP_UNLESS_thm1]
        ;
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) UNLESS q)FPr";
            "((p:*->bool) EXIST_TRANSITION q)FPr"]
            AND_INTRO_THM)) THEN
         UNDISCH_TAC
            "((p:*->bool) UNLESS q)FPr /\ (p EXIST_TRANSITION q)FPr" THEN
         ASM_REWRITE_TAC [(SYM (SPEC_ALL ENSURES))] THEN
         DISCH_TAC THEN
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) ENSURES q)FPr";"((p:*->bool) UNLESS  q)GPr"]
            AND_INTRO_THM)) THEN
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) ENSURES q)FPr /\ (p UNLESS q)GPr";
            "((p:*->bool) ENSURES q)GPr /\ (p UNLESS q)FPr"]
            OR_INTRO_THM1)) THEN
         ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (ASSUME "!GPr:(*->*)list.
            (p ENSURES q)FPr /\ (p UNLESS q)GPr \/
            (p ENSURES q)GPr /\ (p UNLESS q)FPr ==>
              (p ENSURES q)(APPEND FPr GPr)"))) THEN
         UNDISCH_TAC "((p:*->bool) ENSURES q)(APPEND FPr GPr)" THEN
         REWRITE_TAC [ENSURES] THEN
         STRIP_TAC THEN
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC [COMP_UNLESS_thm1]
        ;
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) UNLESS q)GPr";"((p:*->bool) EXIST_TRANSITION q)GPr"]
            AND_INTRO_THM)) THEN
         UNDISCH_TAC
            "((p:*->bool) UNLESS q)GPr /\ (p EXIST_TRANSITION q)GPr" THEN
         ASM_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ENSURES))] THEN
         DISCH_TAC THEN
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) ENSURES q)GPr";"((p:*->bool) UNLESS q) FPr"]
            AND_INTRO_THM)) THEN
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["((p:*->bool) ENSURES q)FPr /\ (p UNLESS q)GPr";
            "((p:*->bool) ENSURES q)GPr /\ (p UNLESS q)FPr"]
            OR_INTRO_THM2)) THEN
         ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (ASSUME "!GPr:(*->*)list.
           (p ENSURES q)FPr /\ (p UNLESS q)GPr \/
           (p ENSURES q)GPr /\ (p UNLESS q)FPr ==>
              (p ENSURES q)(APPEND FPr GPr)"))) THEN
         UNDISCH_TAC "((p:*->bool) ENSURES q)(APPEND FPr GPr)" THEN
         REWRITE_TAC [ENSURES] THEN
         STRIP_TAC THEN
         ASM_REWRITE_TAC []]]);;

%
   Prove:
    !p q FPr GPr.
      (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr
%
let COMP_ENSURES_thm1 = prove_thm
  (`COMP_ENSURES_thm1`,
   "!(p:*->bool) q FPr GPr.
      (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr",
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                       (SPEC_ALL COMP_ENSURES_thm1_lemma_1)
                       (SPEC_ALL COMP_ENSURES_thm1_lemma_2)));;

%
   Prove:

    |- !p q FPr GPr.
         (p ENSURES q)FPr /\ (p UNLESS q)GPr ==> (p ENSURES q)(APPEND FPr GPr)
%
let COMP_ENSURES_cor0 = prove_thm
  (`COMP_ENSURES_cor0`,
   "!(p:*->bool) q FPr GPr.
      (p ENSURES q) FPr /\ (p UNLESS q) GPr
         ==> (p ENSURES q) (APPEND FPr GPr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "((p:*->bool) ENSURES q)FPr";ASSUME "((p:*->bool) UNLESS q)GPr"]
    (SPEC_ALL COMP_ENSURES_thm1)));;


%
   Prove:

    |- !p q FPr GPr.
         (p ENSURES q)GPr /\ (p UNLESS q)FPr ==> (p ENSURES q)(APPEND FPr GPr)
%
let COMP_ENSURES_cor1 = prove_thm
  (`COMP_ENSURES_cor1`,
   "!(p:*->bool) q FPr GPr.
      (p ENSURES q) GPr /\ (p UNLESS q) FPr
         ==> (p ENSURES q) (APPEND FPr GPr)",
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME "((p:*->bool) ENSURES q)GPr";ASSUME "((p:*->bool) UNLESS q)FPr"]
    (SPEC_ALL COMP_ENSURES_thm1)));;

%
   Prove:
     !p q FPr GPr.
      (p INVARIANT q) (APPEND FPr GPr) =
          (p INVARIANT q) FPr /\ (p INVARIANT q) GPr
%
let COMP_UNITY_cor0 = prove_thm
  (`COMP_UNITY_cor0`,
   "!(p0:*->bool) p FPr GPr.
       p INVARIANT (p0, APPEND FPr GPr) =
          p INVARIANT (p0,FPr) /\ p INVARIANT (p0,GPr)",
   REWRITE_TAC [INVARIANT;STABLE;COMP_UNLESS_thm1] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN ASM_REWRITE_TAC []);;


%
   Prove:
        !p FPr GPr.
           p STABLE (APPEND FPr GPr) = p STABLE FPr /\ p STABLE GPr
%
let COMP_UNITY_cor1 = prove_thm
  (`COMP_UNITY_cor1`,
   "!(p:*->bool) FPr GPr.
           p STABLE (APPEND FPr GPr) = p STABLE FPr /\ p STABLE GPr",
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1]);;

%
   Prove:
        !p q FPr GPr.
         (p UNLESS q) FPr /\ p STABLE GPr ==>(p UNLESS q) (APPEND FPr GPr)
%
let COMP_UNITY_cor2 = prove_thm
  (`COMP_UNITY_cor2`,
   "!(p:*->bool) q FPr GPr.
         (p UNLESS q) FPr /\ p STABLE GPr ==>(p UNLESS q) (APPEND FPr GPr)",
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      ASM_REWRITE_TAC []
     ;
      UNDISCH_TAC "((p:*->bool) UNLESS FALSE)GPr" THEN
      SPEC_TAC ("GPr:(*->*)list","GPr:(*->*)list") THEN
      LIST_INDUCT_TAC THENL
        [
         REWRITE_TAC [UNLESS]
        ;
         REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
         CONV_TAC (DEPTH_CONV BETA_CONV) THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            UNDISCH_TAC
               "~(FALSE:*->bool) s ==> (p:*->bool)(h s) \/ FALSE(h s)" THEN
            REWRITE_TAC [FALSE_DEF;NOT_CLAUSES;OR_INTRO_THM1]
           ;
            RES_TAC]]]);;

%
   Prove:
     !p0 p FPr GPr.
       p INVARIANT (p0, FPr) /\ p STABLE GPr
            ==> p INVARIANT (p0, (APPEND FPr GPr))
%
let COMP_UNITY_cor3 = prove_thm
  (`COMP_UNITY_cor3`,
   "!(p0:*->bool) p FPr GPr.
       p INVARIANT (p0, FPr) /\ p STABLE GPr ==>
                    p INVARIANT (p0, (APPEND FPr GPr))",
   REWRITE_TAC [INVARIANT;STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      RES_TAC
     ;
      ASM_REWRITE_TAC []
     ;
      ASM_REWRITE_TAC []]);;


%
   Prove:
       !p q FPr GPr.
        (p ENSURES q) FPr /\ p STABLE GPr ==> (p ENSURES q) (APPEND FPr GPr)
%
let COMP_UNITY_cor4 = prove_thm
  (`COMP_UNITY_cor4`,
   "!(p:*->bool) q FPr GPr.
        (p ENSURES q) FPr /\ p STABLE GPr ==> (p ENSURES q) (APPEND FPr GPr)",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["p:*->bool";"q:*->bool";"FPr:(*->*)list"] ENSURES_cor2)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((p:*->bool) UNLESS q)FPr";"(p:*->bool) STABLE GPr"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["p:*->bool";"q:*->bool";"FPr:(*->*)list";"GPr:(*->*)list"]
         COMP_UNITY_cor2)) THEN
   REWRITE_TAC [ENSURES] THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC "((p:*->bool) ENSURES q)FPr" THEN
   REWRITE_TAC [ENSURES] THEN
   STRIP_TAC THEN
   UNDISCH_TAC "((p:*->bool) EXIST_TRANSITION q)FPr" THEN
   SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [EXIST_TRANSITION]
     ;
      REWRITE_TAC [APPEND;EXIST_TRANSITION] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC THEN
         ASM_REWRITE_TAC []]]);;

%
   Prove:
   "!p q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) GPr
%
let COMP_UNITY_cor5 = prove_thm
  (`COMP_UNITY_cor5`,
   "!(p:*->bool) q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) GPr",
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC);;

%
   Prove:
    !p q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) FPr
%
let COMP_UNITY_cor6 = prove_thm
  (`COMP_UNITY_cor6`,
   "!(p:*->bool) q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) FPr",
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC);;

%
   Prove:
    !p q st FPr. (p UNLESS q)(CONS st FPr) ==> (p UNLESS q) FPr
%
let COMP_UNITY_cor7 = prove_thm
  (`COMP_UNITY_cor7`,
   "!(p:*->bool) q st FPr. (p UNLESS q)(CONS st FPr) ==> (p UNLESS q) FPr",
   REWRITE_TAC [UNLESS] THEN
   REPEAT STRIP_TAC);;

%
   Prove:
        !p FPr GPr.
           (p ENSURES (~* p)) FPr ==> (p ENSURES (~* p)) (APPEND FPr GPr)
%
let COMP_UNITY_cor8 = prove_thm
  (`COMP_UNITY_cor8`,
   "!(p:*->bool) FPr GPr.
        (p ENSURES (~* p)) FPr ==> (p ENSURES (~* p)) (APPEND FPr GPr)",
   GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION]
     ;
      REPEAT GEN_TAC THEN
      REWRITE_TAC [APPEND;ENSURES;UNLESS;UNLESS_STMT;EXIST_TRANSITION] THEN
      BETA_TAC THEN
      REPEAT STRIP_TAC THENL
        [
         REWRITE_TAC [(MP
          (SPEC_ALL (ASSUME "!s:*. p s /\ ~~* p s ==> ~* p(h s)"))
            (CONJ (ASSUME "(p:*->bool) s") (ASSUME "~~* (p:*->bool) s")))]
        ;
         REWRITE_TAC [UNLESS_thm2]
        ;
         ASM_REWRITE_TAC []
        ;
         REWRITE_TAC [(MP
          (SPEC_ALL (ASSUME "!s:*. p s /\ ~~* p s ==> p(h s) \/ ~* p(h s)"))
            (CONJ (ASSUME "(p:*->bool) s") (ASSUME "~~* (p:*->bool) s")))]
        ;
         REWRITE_TAC [UNLESS_thm2]
        ;
         MP_TAC (CONJ (ASSUME "((p:*->bool) UNLESS (~* p))FPr")
                      (ASSUME "((p:*->bool) EXIST_TRANSITION (~* p))FPr")) THEN
         REWRITE_TAC [(SYM (SPEC_ALL ENSURES))] THEN
         DISCH_TAC THEN
         RES_TAC THEN
         REWRITE_TAC [REWRITE_RULE [ENSURES] (SPEC_ALL
          (ASSUME "!GPr. ((p:*->bool) ENSURES (~* p))(APPEND FPr GPr)"))]
        ]
      ]);;

%
   Prove:
        !p q FPr GPr.
           p STABLE FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)
%
let COMP_UNITY_cor9 = prove_thm
  (`COMP_UNITY_cor9`,
   "!(p:*->bool) q FPr GPr.
         p STABLE FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)",
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      UNDISCH_TAC "((p:*->bool) UNLESS FALSE)FPr" THEN
      SPEC_TAC ("FPr:(*->*)list","FPr:(*->*)list") THEN
      LIST_INDUCT_TAC THENL
        [
         REWRITE_TAC [UNLESS]
        ;
         REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
         BETA_TAC THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            UNDISCH_TAC
               "~(FALSE:*->bool) s ==> (p:*->bool)(h s) \/ FALSE(h s)" THEN
            REWRITE_TAC [FALSE_DEF;NOT_CLAUSES;OR_INTRO_THM1]
           ;
            RES_TAC
           ]
        ]
     ;
      ASM_REWRITE_TAC []
     ]);;


%
   Prove:
    !p q FPr GPr.
         (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) (APPEND GPr FPr)
%
let COMP_UNITY_cor10 = prove_thm
  (`COMP_UNITY_cor10`,
   "!(p:*->bool) q FPr GPr.
         (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) (APPEND GPr FPr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

%
   Prove:
    !p q FPr GPr.
         (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) (APPEND GPr FPr)
%
let COMP_UNITY_cor11 = prove_thm
  (`COMP_UNITY_cor11`,
   "!(p:*->bool) q FPr GPr.
         (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) (APPEND GPr FPr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [COMP_ENSURES_thm1] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

%
   Prove:
    !p q FPr GPr.
      (p LEADSTO q) (APPEND FPr GPr) = (p LEADSTO q) (APPEND GPr FPr)
%

%
  |- (!p' q'.
     ((p' ENSURES q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)) /\
     (!r.
       (p' LEADSTO r)(APPEND Pr1 Pr2) /\ (p' LEADSTO r)(APPEND Pr2 Pr1) /\
       (r LEADSTO q')(APPEND Pr1 Pr2) /\ (r LEADSTO q')(APPEND Pr2 Pr1) ==>
       (p' LEADSTO q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)) /\
     (!P.
       (!i. ((P i) LEADSTO q')(APPEND Pr1 Pr2)) /\
       (!i. ((P i) LEADSTO q')(APPEND Pr2 Pr1)) ==>
          (($?* P) LEADSTO q')(APPEND Pr1 Pr2) ==>
          (($?* P) LEADSTO q')(APPEND Pr2 Pr1)))
     ==>
       (p LEADSTO q)(APPEND Pr1 Pr2) ==> (p LEADSTO q)(APPEND Pr2 Pr1)
%
let COMP_UNITY_cor12_lemma00 = (BETA_RULE (SPECL
  ["\(p:*->bool) q. (p LEADSTO q)(APPEND Pr2 Pr1)";
   "p:*->bool";"q:*->bool";"APPEND (Pr1:(*->*)list) Pr2"] LEADSTO_thm37));;

let COMP_UNITY_cor12_lemma01 = TAC_PROOF
  (([],
   "!(p':*->bool) q' Pr1 Pr2.
      (p' ENSURES q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [COMP_UNITY_cor11] (ASSUME
    "((p':*->bool) ENSURES q')(APPEND Pr1 Pr2)")) THEN
   IMP_RES_TAC LEADSTO_thm0);;

let COMP_UNITY_cor12_lemma02 = TAC_PROOF
  (([],
   "!(p':*->bool) q' Pr1 Pr2.
     (!r.
       (p' LEADSTO r)(APPEND Pr1 Pr2) /\ (p' LEADSTO r)(APPEND Pr2 Pr1) /\
       (r LEADSTO q')(APPEND Pr1 Pr2) /\ (r LEADSTO q')(APPEND Pr2 Pr1)
          ==> (p' LEADSTO q')(APPEND Pr2 Pr1))"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm1);;

let COMP_UNITY_cor12_lemma03 = TAC_PROOF
  (([],
   "!(p':*->bool) q' Pr1 Pr2.
     (!P:(*->bool)->bool.
       (!p''. p'' In P ==> (p'' LEADSTO q')(APPEND Pr1 Pr2)) /\
       (!p''. p'' In P ==> (p'' LEADSTO q')(APPEND Pr2 Pr1))
            ==> ((LUB P) LEADSTO q')(APPEND Pr2 Pr1))"),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm3a);;

%
  |- !p q Pr1 Pr2.
       (p LEADSTO q)(APPEND Pr1 Pr2) ==> (p LEADSTO q)(APPEND Pr2 Pr1)
%
let COMP_UNITY_cor12_lemma04 = (GEN_ALL (REWRITE_RULE
   [COMP_UNITY_cor12_lemma01;COMP_UNITY_cor12_lemma02;COMP_UNITY_cor12_lemma03]
    (SPEC_ALL COMP_UNITY_cor12_lemma00)));;

%
 |- !p q Pr1 Pr2. (p LEADSTO q)(APPEND Pr1 Pr2) = (p LEADSTO q)(APPEND Pr2 Pr1)
%
let COMP_UNITY_cor12 = prove_thm
  (`COMP_UNITY_cor12`,
   "!(p:*->bool) q Pr1 Pr2.
       (p LEADSTO q)(APPEND Pr1 Pr2) = (p LEADSTO q)(APPEND Pr2 Pr1)",
   REPEAT GEN_TAC THEN
   EQ_TAC THEN REWRITE_TAC [COMP_UNITY_cor12_lemma04]);;

%
  |- !p FPr GPr. p STABLE (APPEND FPr GPr) = p STABLE (APPEND GPr FPr)
%
let COMP_UNITY_cor13 = prove_thm
  (`COMP_UNITY_cor13`,
   "!(p:*->bool) FPr GPr.
      (p STABLE (APPEND FPr GPr)) = (p STABLE (APPEND GPr FPr))",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [COMP_UNITY_cor10] THEN
   ASM_REWRITE_TAC []);;

%
  |- !p0 p FPr GPr.
      p INVARIANT (p0,APPEND FPr GPr) = p INVARIANT (p0,APPEND GPr FPr)
%
let COMP_UNITY_cor14 = prove_thm
  (`COMP_UNITY_cor14`,
   "!(p0:*->bool) p FPr GPr.
      (p INVARIANT (p0, (APPEND FPr GPr)))
    =
      (p INVARIANT (p0, (APPEND GPr FPr)))",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [INVARIANT] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [COMP_UNITY_cor13] THEN
   ASM_REWRITE_TAC []);;


close_theory();;
