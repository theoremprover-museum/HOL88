% -*- Emacs Mode: fundamental -*- %


%-----------------------------------------------------------------------------%
%
   File:         mk_nensures.ml

   Description:  This file defines ENSURES and the theorems and corrollaries
                 described in [CM88].

   Author:       (c) Copyright by Flemming Andersen
   Date:         June 29, 1989
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
autoload_defs_and_thms `unless`;;
%

system `/bin/rm ensures.th`;;

new_theory`ensures`;;

%-----------------------------------------------------------------------------%
% The definition of ENSURES is based on the definition:

      p ensures q in Pr = <p unless q in Pr /\ (?s in Pr: {p /\ ~q} s {q})>

  where p and q are state dependent first order logic predicates and
  s in the program Pr are conditionally enabled statements transforming
  a state into a new state. ENSURES then requires safety and the existance
  of at least one state transition statement s which makes q valid.
%
let EXIST_TRANSITION =
  new_recursive_definition true list_Axiom `EXIST_TRANSITION`
  "(EXIST_TRANSITION (p:*->bool) q [] = F) /\
   (EXIST_TRANSITION p q (CONS (st:*->*) Pr) =
     (!s. (p s /\ ~q s) ==> q (st s)) \/ (EXIST_TRANSITION p q Pr))";;

let ENSURES = new_infix_definition
  (`ENSURES`,
   "ENSURES (p:*->bool) q (Pr:(*->*)list) =
      ((p UNLESS q) Pr) /\ ((p EXIST_TRANSITION q) Pr)");;

%-----------------------------------------------------------------------------%
%
  Lemmas
%
%-----------------------------------------------------------------------------%

let ENSURES_lemma0 = TAC_PROOF
  (([],
   "!(p:*->bool) q r st.
          ((!s. p s /\ ~q s ==> q (st s)) /\ (!s. q s ==> r s)) ==>
           (!s. p s /\ ~r s ==> r (st s))"),
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (CONTRAPOS (SPEC_ALL (ASSUME "!s:*. q s ==> r s"))) THEN
    ASSUME_TAC (SPEC "(st:*->*) s" (ASSUME "!s:*. q s ==> r s")) THEN
    RES_TAC THEN
    RES_TAC);;

let ENSURES_lemma1 = TAC_PROOF
  (([],
   "!(p:*->bool) p' q q'.
     (!s. p s /\ ~q s ==> p (st s) \/ q (st s)) ==>
      ((!s. p' s /\ ~q' s ==> p'(st s) \/ q'(st s)) ==>
       ((!s. p' s /\ ~q' s ==> q'(st s)) ==>
        (!s. p s /\ p' s /\ (~p s \/ ~q' s) /\ 
        (~p' s \/ ~q s) /\ (~q s \/ ~q' s) ==>
            p (st s) /\ q'(st s) \/ p'(st s) /\
            q (st s) \/ q (st s) /\ q'(st s))))"),
     REPEAT STRIP_TAC THENL
       [
        RES_TAC
       ;
        RES_TAC
       ;
        RES_TAC
       ;
        RES_TAC
       ;
        RES_TAC
       ;
        RES_TAC
       ;
        REWRITE_TAC [REWRITE_RULE
         [ASSUME "~(q:*->bool)s";ASSUME "~(q':*->bool)s";
          ASSUME "(p':*->bool)s";ASSUME "(p:*->bool)s"] (SPEC_ALL
          (ASSUME "!s:*. p' s /\ ~q' s ==> q'(st s)"))] THEN
        STRIP_ASSUME_TAC (REWRITE_RULE
         [ASSUME "~(q:*->bool)s";ASSUME "~(q':*->bool)s";
          ASSUME "(p':*->bool)s";ASSUME "(p:*->bool)s"] (SPEC_ALL (ASSUME
            "!s:*. p s /\ ~q s ==> p(st s) \/ q(st s)"))) THENL
         [
          ASM_REWRITE_TAC []
         ;
          ASM_REWRITE_TAC []
         ]
       ;
        REWRITE_TAC [REWRITE_RULE
         [ASSUME "~(q:*->bool)s";ASSUME "~(q':*->bool)s";
          ASSUME "(p':*->bool)s";ASSUME "(p:*->bool)s"] (SPEC_ALL
          (ASSUME "!s:*. p' s /\ ~q' s ==> q'(st s)"))] THEN
        STRIP_ASSUME_TAC (REWRITE_RULE
         [ASSUME "~(q:*->bool)s";ASSUME "~(q':*->bool)s";
          ASSUME "(p':*->bool)s";ASSUME "(p:*->bool)s"] (SPEC_ALL (ASSUME
            "!s:*. p s /\ ~q s ==> p(st s) \/ q(st s)"))) THENL
         [
          ASM_REWRITE_TAC []
         ;
          ASM_REWRITE_TAC []
         ]
       ]);;

let ENSURES_lemma2 = TAC_PROOF
  (([],
   "!(p:*->bool) q r st.
       (!s. p s /\ ~q s ==> q (st s)) ==>
         (!s. (p s \/ r s) /\ ~(q s \/ r s) ==> q (st s) \/ r (st s))"),
     REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                  (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
     REPEAT STRIP_TAC THENL
      [
       RES_TAC THEN
       ASM_REWRITE_TAC []
      ;
       RES_TAC
     ]);;

let ENSURES_lemma3 = TAC_PROOF
  (([],
   "!(p:*->bool) q r Pr. (p ENSURES (q \/* r)) Pr ==>
              (((p /\* (~* q)) \/* (p /\* q)) ENSURES (q \/* r)) Pr"),
   REWRITE_TAC [AND_COMPL_OR_lemma]);;

%-----------------------------------------------------------------------------%
%
  Theorems about EXIST_TRANSITION
%
%-----------------------------------------------------------------------------%

%
  EXIST_TRANSITION Consequence Weakening Theorem:

               p EXIST_TRANSITION q in Pr, q ==> r
              -------------------------------------
                   p EXIST_TRANSITION r in Pr
%
let EXIST_TRANSITION_thm1 = prove_thm
 (`EXIST_TRANSITION_thm1`,
  "!(p:*->bool) q r Pr.
     ((p EXIST_TRANSITION q) Pr /\ (!s. (q s) ==> (r s))) ==>
       ((p EXIST_TRANSITION r) Pr)",
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THENL
    [
     REWRITE_TAC [EXIST_TRANSITION]
    ;
     X_GEN_TAC "st:*->*" THEN
     REWRITE_TAC [EXIST_TRANSITION] THEN
     REPEAT STRIP_TAC THENL
       [
        ASSUME_TAC (UNDISCH_ALL (SPEC "!s:*. q s ==> r s"
          (SPEC "!s:*. p s /\ ~q s ==> q (st s)" AND_INTRO_THM))) THEN
        STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma0)) THEN
        ASM_REWRITE_TAC []
       ;
        RES_TAC THEN
        ASM_REWRITE_TAC []
       ]
    ]);;

%
  Impossibility EXIST_TRANSITION Theorem:

               p EXIST_TRANSITION false in Pr
              --------------------------------
                          ~p 
%
let EXIST_TRANSITION_thm2 = prove_thm
  (`EXIST_TRANSITION_thm2`,
   "!(p:*->bool) Pr. ((p EXIST_TRANSITION FALSE) Pr) ==> !s. (~* p)s",
   STRIP_TAC THEN
   REWRITE_TAC [FALSE_DEF;~*] THEN
   REWRITE_TAC [BETA_CONV "(\s:*. ~p s)s"] THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [EXIST_TRANSITION]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [EXIST_TRANSITION] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC
     ]);;

%
  Always EXIST_TRANSITION Theorem:

               false EXIST_TRANSITION p in Pr
%
let EXIST_TRANSITION_thm3 = prove_thm
  (`EXIST_TRANSITION_thm3`,
   "!(p:*->bool) st Pr. (FALSE EXIST_TRANSITION p) (CONS st Pr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION;FALSE_DEF]);;

%-----------------------------------------------------------------------------%
%
  Theorems about ENSURES
%
%-----------------------------------------------------------------------------%

%
  Reflexivity Theorem:

               p ensures p in Pr

  The theorem is only valid for non-empty programs
%
let ENSURES_thm0 = prove_thm
  (`ENSURES_thm0`,
   "!(p:*->bool) q. (p ENSURES q) [] = F",
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS;EXIST_TRANSITION]);;

let ENSURES_thm1 = prove_thm
  (`ENSURES_thm1`,
   "!(p:*->bool) st Pr. (p ENSURES p) (CONS st Pr)",
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS;EXIST_TRANSITION] THEN
     REWRITE_TAC [UNLESS_thm1;UNLESS_STMT] THEN
     REWRITE_TAC [BETA_CONV "(\s:*. (p s /\ ~p s) ==> p (st s))s"] THEN
     REWRITE_TAC[NOT_AND;IMP_CLAUSES]);;

%
  Consequence Weakening Theorem:

               p ensures q in Pr, q ==> r
              ----------------------------
                   p ensures r in Pr
%
let ENSURES_thm2 = prove_thm
  (`ENSURES_thm2`,
   "!(p:*->bool) q r Pr.
         ((p ENSURES q) Pr /\ (!s:*. (q s) ==> (r s))) ==> ((p ENSURES r) Pr)",
   REWRITE_TAC [ENSURES] THEN
   REPEAT STRIP_TAC THENL
     [
      ASSUME_TAC (UNDISCH_ALL (SPEC "!s:*. q s ==> r s"
        (SPEC "((p:*->bool) UNLESS q) Pr" AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm3))
     ;
      ASSUME_TAC (UNDISCH_ALL (SPEC "!s:*. q s ==> r s"
        (SPEC "((p:*->bool) EXIST_TRANSITION q) Pr" AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL EXIST_TRANSITION_thm1))
     ]);;

%
  Impossibility Theorem:

               p ensures false in Pr
              ----------------------
                       ~p 
%
let ENSURES_thm3 = prove_thm
  (`ENSURES_thm3`,
   "!(p:*->bool) Pr. ((p ENSURES FALSE) Pr) ==> !s. (~* p)s",
   STRIP_TAC THEN LIST_INDUCT_TAC THENL
    [
     REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION;~*;FALSE_DEF]
    ;
     X_GEN_TAC "st:*->*" THEN
     REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION;FALSE_DEF;~*] THEN
     REPEAT STRIP_TAC THENL
       [
        REWRITE_TAC[BETA_CONV "(\s:*. ~p s)s"] THEN
        ASM_REWRITE_TAC []
       ;
        ASSUME_TAC (SPEC_ALL EXIST_TRANSITION_thm2) THEN
        UNDISCH_TAC "((p:*->bool) EXIST_TRANSITION (\s. F)) Pr" THEN
        REWRITE_TAC [(SYM (SPEC_ALL ~*));(SYM (SPEC_ALL FALSE_DEF))] THEN
        REPEAT STRIP_TAC THEN
        RES_TAC THEN
        ASM_REWRITE_TAC []
       ]
    ]);;

%
  Conjunction Theorem:

                   p unless q in Pr, p' ensures q' in Pr
              -----------------------------------------------
               p/\p' ensures (p/\q')\/(p'/\q)\/(q/\q') in Pr
%
let ENSURES_thm4 = prove_thm
  (`ENSURES_thm4`,
   "!(p:*->bool) q p' q' Pr.
    (p UNLESS q) Pr /\ (p' ENSURES q') Pr ==>
      ((p /\* p') ENSURES (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))) Pr",
   STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION;/\*;\/*]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION] THEN
      DISCH_TAC THEN
      REPEAT STRIP_TAC THENL
        [
         UNDISCH_TAC
           "((!s:*. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS  q ) Pr) /\
            ((!s.  (p' UNLESS_STMT q') st s) /\ (p' UNLESS  q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q' (st s)) \/ (p' EXIST_TRANSITION q') Pr)"
           THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (UNDISCH_ALL (SPEC "!s:*. (p' UNLESS_STMT q') st s"
                                    (SPEC "!s:*. (p  UNLESS_STMT q ) st s"
                                     AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm3)) THEN
            ASM_REWRITE_TAC []
           ;
            ASSUME_TAC (UNDISCH_ALL (SPEC "!s:*. (p' UNLESS_STMT q') st s"
                                    (SPEC "!s:*. (p  UNLESS_STMT q ) st s"
                                     AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm3)) THEN
            ASM_REWRITE_TAC []
           ]
        ;
         UNDISCH_TAC
           "((!s:*. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS  q ) Pr) /\
            ((!s.   (p' UNLESS_STMT q') st s) /\ (p' UNLESS  q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q'(st s)) \/ (p' EXIST_TRANSITION q')Pr)"
               THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (UNDISCH_ALL (SPEC "((p':*->bool) UNLESS q') Pr"
                                    (SPEC "((p:*->bool)  UNLESS q ) Pr"
                        AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4))
           ;
            ASSUME_TAC (UNDISCH_ALL (SPEC "((p':*->bool) UNLESS q') Pr"
                                    (SPEC "((p:*->bool)  UNLESS q) Pr"
                                     AND_INTRO_THM))) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4))
           ]
        ;
         UNDISCH_TAC
           "((!s:*. (p  UNLESS_STMT q ) st s) /\ (p  UNLESS q ) Pr) /\
            ((!s.   (p' UNLESS_STMT q') st s) /\ (p' UNLESS q') Pr) /\
            ((!s. p' s /\ ~q' s ==> q'(st s)) \/ (p' EXIST_TRANSITION q')Pr)"
                 THEN
         REPEAT STRIP_TAC THENL
           [
            UNDISCH_TAC "!s:*. p' s /\ ~q' s ==> q'(st s)" THEN
            UNDISCH_TAC "!s:*. (p' UNLESS_STMT q') st s" THEN
            UNDISCH_TAC "!s:*. (p  UNLESS_STMT q ) st s" THEN
            REWRITE_TAC [UNLESS_STMT;/\*;\/*] THEN
            CONV_TAC (DEPTH_CONV BETA_CONV) THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                         (SYM (SPEC_ALL DISJ_ASSOC));
                         NOT_CLAUSES;DE_MORGAN_THM] THEN
            REPEAT STRIP_TAC THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma1)) THEN
            ASM_REWRITE_TAC []
           ;
            RES_TAC THEN
            ASSUME_TAC (UNDISCH_ALL
               (SPEC "((p':*->bool) EXIST_TRANSITION q')Pr"
               (SPEC "((p':*->bool) UNLESS q')Pr"
                AND_INTRO_THM))) THEN
            UNDISCH_TAC
              "((p':*->bool) UNLESS q') Pr /\ (p' EXIST_TRANSITION q') Pr" THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
            STRIP_TAC THEN
            RES_TAC THEN
            UNDISCH_TAC "(((p:*->bool) /\* p') ENSURES (((p /\* q') \/*
                           (p' /\* q)) \/* (q /\* q')))Pr" THEN
            REWRITE_TAC [ENSURES] THEN
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]
        ]
     ]);;

%
  Conjunction Theorem:

                   p ensures q in Pr
              -------------------------
               p\/r ensures q\/r in Pr
%
let ENSURES_thm5 = prove_thm
  (`ENSURES_thm5`,
   "!(p:*->bool) q r Pr.
      ((p ENSURES q) Pr) ==> (((p \/* r) ENSURES (q \/* r)) Pr)",
   STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION] THEN
      DISCH_TAC THEN
      REPEAT STRIP_TAC THENL
        [
         UNDISCH_TAC
           "((!s:*. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
            ((!s. p s /\ ~q s ==> q (st s)) \/ (p EXIST_TRANSITION q)Pr)" THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (SPECL ["r:*->bool";"st:*->*"] UNLESS_STMT_thm0) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              ["!s:*. (p UNLESS_STMT q) st s";"!s:*. (r UNLESS_STMT r) st s"]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              ["p:*->bool";"q:*->bool";"r:*->bool";"r:*->bool";"st:*->*"]
               UNLESS_STMT_thm2)) THEN
            ASM_REWRITE_TAC []
           ;
            ASSUME_TAC (SPECL ["r:*->bool";"st:*->*"] UNLESS_STMT_thm0) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              ["!s:*. (p UNLESS_STMT q) st s";"!s:*. (r UNLESS_STMT r) st s"]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              ["p:*->bool";"q:*->bool";"r:*->bool";"r:*->bool";"st:*->*"]
               UNLESS_STMT_thm2)) THEN
            ASM_REWRITE_TAC []
           ]
        ;
         UNDISCH_TAC
           "((!s:*. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
            ((!s. p s /\ ~q s ==> q (st s)) \/ (p EXIST_TRANSITION q)Pr)" THEN
         REPEAT STRIP_TAC THENL
           [
            ASSUME_TAC (SPECL ["r:*->bool";"Pr:(*->*)list"] UNLESS_thm1) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              ["((p:*->bool) UNLESS q) Pr";"((r:*->bool) UNLESS r) Pr"]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              ["p:*->bool";"q:*->bool";"r:*->bool";"r:*->bool";"Pr:(*->*)list"]
               UNLESS_thm7))
           ;
            ASSUME_TAC (SPECL ["r:*->bool";"Pr:(*->*)list"] UNLESS_thm1) THEN
            ASSUME_TAC (UNDISCH_ALL (SPECL
              ["((p:*->bool) UNLESS q) Pr";"((r:*->bool) UNLESS r) Pr"]
               AND_INTRO_THM)) THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
              ["p:*->bool";"q:*->bool";"r:*->bool";"r:*->bool";"Pr:(*->*)list"]
               UNLESS_thm7))
           ]
        ;
         UNDISCH_TAC
          "((!s:*. (p UNLESS_STMT q) st s) /\ (p UNLESS q) Pr) /\
           ((!s. p s /\ ~q s ==> q (st s)) \/ (p EXIST_TRANSITION q)Pr)" THEN
         REPEAT STRIP_TAC THENL
           [
            REWRITE_TAC [\/*] THEN
            REWRITE_TAC [BETA_CONV "(\s:*. p s \/ r s) s"] THEN
            STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma2)) THEN
            ASM_REWRITE_TAC []
           ;
            ASSUME_TAC (UNDISCH_ALL  (SPECL
              ["((p:*->bool) UNLESS q)Pr";"((p:*->bool) EXIST_TRANSITION q)Pr"]
               AND_INTRO_THM)) THEN
            UNDISCH_TAC
              "((p:*->bool) UNLESS q) Pr /\ (p EXIST_TRANSITION q) Pr" THEN
            REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
            STRIP_TAC THEN
            RES_TAC THEN
            UNDISCH_TAC "(((p:*->bool) \/* r) ENSURES (q \/* r)) Pr" THEN
            REWRITE_TAC [ENSURES] THEN
            REPEAT STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]
        ]
     ]);;

%
 -----------------------------------------------------------------------------
  Corollaries about ENSURES
 -----------------------------------------------------------------------------
%

%
  Implies Corollary:

                   p => q
              -------------------
               p ensures q in Pr

  This corollary is only valid for non-empty programs.
%
let ENSURES_cor1 = prove_thm
  (`ENSURES_cor1`,
   "!(p:*->bool) q st Pr. (!s. p s ==> q s) ==> (p ENSURES q) (CONS st Pr)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC_ALL ENSURES_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) ENSURES p)(CONS st Pr)";"!s:*. p s ==> q s"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
     ["p:*->bool";"p:*->bool";"q:*->bool";"CONS (st:*->*) Pr"]
      ENSURES_thm2)));;

let ENSURES_cor2 = prove_thm
  (`ENSURES_cor2`,
   "!(p:*->bool) q Pr. (p ENSURES q) Pr ==> (p UNLESS q) Pr",
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ]
     ]);;

let ENSURES_cor3 = prove_thm
  (`ENSURES_cor3`,
   "!(p:*->bool) q r Pr. ((p \/* q) ENSURES r)Pr ==> (p ENSURES (q \/* r))Pr",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) \/* q)";"r:*->bool";"Pr:(*->*)list"] ENSURES_cor2)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["p:*->bool";"q:*->bool";"r:*->bool";"Pr:(*->*)list"] UNLESS_cor4)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) UNLESS (q \/* r))Pr";"(((p:*->bool) \/* q) ENSURES r)Pr"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["p:*->bool";"((q:*->bool) \/* r)";"((p:*->bool) \/* q)";"r:*->bool";
      "Pr:(*->*)list"] ENSURES_thm4)) THEN
   UNDISCH_TAC "(((p:*->bool) /\* (p \/* q)) ENSURES
                (((p /\* r) \/* ((p \/* q) /\* (q \/* r))) \/*
                 ((q \/* r) /\* r))) Pr" THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;AND_ASSOC_lemma] THEN
   PURE_ONCE_REWRITE_TAC [SPECL
         ["((q:*->bool) \/* r)";"r:*->bool"] AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [AND_OR_EQ_AND_COMM_OR_lemma] THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL ["p:*->bool";"q:*->bool";"r:*->bool"]
                           IMPLY_WEAK_lemma5) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["((p:*->bool) ENSURES
      ((p /\* r) \/* (((p \/* q) /\* (q \/* r)) \/* r)))Pr";
     "!s:*. ((p /\* r) \/* (((p \/* q) /\* (q \/* r)) \/* r))s ==> (q \/* r)s"]
     AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p:*->bool";"(((p:*->bool) /\* r) \/* (((p \/* q) /\* (q \/* r)) \/* r))";
     "((q:*->bool) \/* r)";"Pr:(*->*)list"]
     ENSURES_thm2)));;

let ENSURES_cor4 = prove_thm
  (`ENSURES_cor4`,
   "!(p:*->bool) q r Pr. (p ENSURES (q \/* r)) Pr ==>
              ((p /\* (~* q)) ENSURES (q \/* r)) Pr",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) /\* (~* q))";"((p:*->bool) /\* q)";
      "((q:*->bool) \/* r)";"Pr:(*->*)list"] ENSURES_cor3)) THEN
   UNDISCH_TAC
     "(((p:*->bool) /\* (~* q)) ENSURES ((p /\* q) \/* (q \/* r)))Pr" THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_ASSOC_lemma))] THEN
   REWRITE_TAC [P_AND_Q_OR_Q_lemma]);;

%
  Consequence Weakening Corollary:

                  p ensures q in Pr
              -------------------------
               p ensures (q \/ r) in Pr
%
let ENSURES_cor5 = prove_thm
 (`ENSURES_cor5`,
   "!(p:*->bool) q r Pr. (p ENSURES q) Pr ==> (p ENSURES (q \/* r)) Pr",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL ["q:*->bool";"r:*->bool"] IMPLY_WEAK_lemma_b) THEN
   ASSUME_TAC (SPECL
     ["p:*->bool";"q:*->bool";"(q:*->bool) \/* r"] ENSURES_thm2) THEN
   RES_TAC);;

%
  Always Corollary:

                  false ensures p in Pr
%
let ENSURES_cor6 = prove_thm
  (`ENSURES_cor6`,
   "!(p:*->bool) st Pr. (FALSE ENSURES p) (CONS st Pr)",
   REWRITE_TAC [ENSURES;UNLESS_cor7;EXIST_TRANSITION_thm3]);;

let ENSURES_cor7 = prove_thm
  (`ENSURES_cor7`,
   "!(p:*->bool) q r Pr.
        (p ENSURES q) Pr /\ (r STABLE Pr) ==> ((p /\* r) ENSURES (q /\* r))Pr",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (ONCE_REWRITE_RULE [AND_COMM_lemma]
      (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma] 
        (ONCE_REWRITE_RULE [OR_AND_COMM_lemma] 
          (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma] (SPECL
            ["r:*->bool";"FALSE:*->bool";"p:*->bool";"q:*->bool";
             "Pr:(*->*)list"] ENSURES_thm4))))));;

close_theory();;

