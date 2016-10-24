% -*- Emacs Mode: fundamental -*- %


%-----------------------------------------------------------------------------%
%
   File:         mk_unless.ml
   Description:  

   This file defines the theorems for the UNLESS definition.

   Author:       (c) Copyright by Flemming Andersen
   Date:         June 29, 1989
%
%-----------------------------------------------------------------------------%

%
loadf`aux_definitions`;;

autoload_defs_and_thms `state_logic`;;
%

system `/bin/rm unless.th`;;

new_theory`unless`;;

%-----------------------------------------------------------------------------%
% The definition of UNLESS is based on the definition:

      p UNLESS Q in Pr = <!s in Pr: {p /\ ~q} s {p \/ q}>

  where p /\* q are state dependent first \/*der logic predicates /\* all
  s in the program Pr are conditionally enabled statements transforming
  a state into a new state.
%

%
  To define UNLESS as a relation UNLESS_STMT to be satisfied for a finite
  number of program statements, we define the UNLESS_STMT to be fulfilled as
  a separate HOARE tripple relation between pre- /\* post predicates to be 
  satisfied for state transitions. The pre- /\* post predicates of the
  UNLESS_STMT relation must be satisfiable for all states possible in the
  finite state space of the program.
%
let UNLESS_STMT = new_infix_definition
  (`UNLESS_STMT`,
   "UNLESS_STMT (p:*->bool) q st =
      \s:*. (p s /\ ~q s) ==> (p (st s) \/ q (st s))");;

%
  Since a program is defined as a set (list) of statements, we
  recursively define the UNLESS relation itself using the UNLESS_STMT
  relation to be satisfied for every statement in the program.

  As the bottom of the recursion we choose the empty program always to be
  satisfied. For every statement in the program the UNLESS_STMT relation
  must be satisfied in all possible states.
%

let UNLESS = new_recursive_definition true list_Axiom `UNLESS`
   "(UNLESS (p:*->bool) q  []                 = T) /\
    (UNLESS  p          q (CONS (st:*->*) Pr) =
       (!s:*. (p UNLESS_STMT q) st s) /\ (UNLESS p q Pr))";;

%
  The state predicate STABLE is a special case of UNLESS.

       stable p in Pr = p unless false in Pr
%
let STABLE = new_infix_definition
  (`STABLE`, "STABLE (p:*->bool) Pr = (p UNLESS FALSE) Pr");;

%
  The state predicate INVARIANT is a special case of UNLESS too.
  However invariant is dependent of a program and its initial state.

       invariant P in (initial condition, Pr) =
           (initial condition ==> p) /\ (p stable in Pr)
%
let INVARIANT = new_infix_definition
  (`INVARIANT`,
   "INVARIANT (p:*->bool) (p0, Pr) = (!s. p0 s ==> p s) /\ (p STABLE Pr)");;

%
 -----------------------------------------------------------------------------
  Lemmas used in the UNLESS Theory
 -----------------------------------------------------------------------------
%

let IMP_IMP_CONJIMP_lemma = TAC_PROOF
  (([],
   "!p q ps qs p' q' p's q's.
        (p /\ ~q ==> ps \/ qs) ==> (p' /\ ~q' ==> p's \/ q's) ==>
          (p /\ p' /\ (~p \/ ~q') /\ (~p' \/ ~q) /\ (~q \/ ~q') ==>
                ps /\ p's \/ ps /\ q's \/ p's /\ qs \/ qs /\ q's)"),
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
      RES_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ]
     ;
      RES_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ]
     ]);;

let NOT_NOT_OR_lemma = TAC_PROOF
  (([],
   "!t1 t2 t3. t1 \/ t2 \/ t3 = ~(~t1 /\ ~t2) \/ t3"),
   REWRITE_TAC [NOT_CLAUSES;DE_MORGAN_THM;(SYM (SPEC_ALL DISJ_ASSOC))]);;

let CONJ_IMPLY_THM = TAC_PROOF
  (([],
   "!p p' q q'.
     ((p \/ p') /\ (p \/ ~q') /\ (p' \/ ~q) /\ (~q \/ ~q')) =
     ((p /\ ~q) \/ (p' /\ ~q'))"),
    REPEAT GEN_TAC THEN
    EQ_TAC THEN
    REPEAT STRIP_TAC THEN REPEAT (ASM_REWRITE_TAC []));;


let IMP_IMP_DISJIMP_lemma = TAC_PROOF
  (([],
   "!p q ps qs p' q' p's q's.
    (p /\ ~q ==> ps \/ qs) /\ (p' /\ ~q' ==> p's \/ q's) ==>
      ((p \/ p') /\ (p \/ ~q') /\ (p' \/ ~q) /\ (~q \/ ~q') ==>
                (ps \/ p's \/ ~ps /\ q's \/ ~p's /\ qs \/ qs /\ q's))"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [CONJ_IMPLY_THM] THEN
   DISCH_TAC THEN
   DISCH_TAC THEN
   REWRITE_TAC [
     SPECL ["ps:bool";"p's:bool";"~ps /\ q's \/ ~p's /\ qs \/ qs /\ q's"]
             NOT_NOT_OR_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL IMP_DISJ_THM))] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (CONJUNCT1 
     (ASSUME "(p /\ ~q ==> ps \/ qs) /\ (p' /\ ~q' ==> p's \/ q's)")) THEN
   ASSUME_TAC (CONJUNCT2
     (ASSUME "(p /\ ~q ==> ps \/ qs) /\ (p' /\ ~q' ==> p's \/ q's)")) THEN
   UNDISCH_TAC "p /\ ~q \/ p' /\ ~q'" THEN
   REPEAT STRIP_TAC THENL
     [
      RES_TAC THENL
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
         RES_TAC
        ;
         RES_TAC
        ;
         RES_TAC
        ;
         ASM_REWRITE_TAC []
        ]
     ;
      RES_TAC THENL
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
         RES_TAC
        ;
         RES_TAC
        ;
         RES_TAC
        ;
         ASM_REWRITE_TAC []
        ]
     ]);;

%
 -----------------------------------------------------------------------------
  Theorems about UNLESS_STMT
 -----------------------------------------------------------------------------
%

%
  The reflexivity theorem:

               p unless_stmt P in Prog
%
let UNLESS_STMT_thm0 = prove_thm
  (`UNLESS_STMT_thm0`,
    "!(p:*->bool) st s. (p UNLESS_STMT p)st s",
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [UNLESS_STMT] THEN
    REWRITE_TAC [BETA_CONV "(\s:*. p s /\ ~(p s) ==> p (st s))s"] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC);;

%
  Theorem:
               p unless_stmt Q in stmt, q ==> r
              ------------------------------ 
                   p unless_stmt r in stmt
%
let UNLESS_STMT_thm1 = prove_thm
  (`UNLESS_STMT_thm1`,
   "!(p:*->bool) q r st.
      ((!s. (p UNLESS_STMT q) st s) /\ (!s. (q s) ==> (r s))) ==>
       (!s. (p UNLESS_STMT r) st s)",
   REWRITE_TAC [UNLESS_STMT] THEN
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC (SPEC_ALL
     (ASSUME "!s. (\s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s))s")) THEN
   UNDISCH_TAC "(\s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s))s" THEN
   PURE_REWRITE_TAC [
     BETA_CONV "(\s. (p s /\ ~q s) ==> (P((st:*->*)s) \/  q (st s)))s"] THEN
   REPEAT STRIP_TAC THEN
   STRIP_ASSUME_TAC (CONTRAPOS (SPEC "s:*"
      (ASSUME "!s:*. (q s) ==> (r s)"))) THEN
   RES_TAC THENL
     [
      ASM_REWRITE_TAC []
     ;
      RES_TAC THENL
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

%
  Theorem:
               p unless_stmt Q in st, p' unless_stmt q' in st 
              ------------------------------------------------
                       p\/p' unless_stmt q\/q' in st
%
let UNLESS_STMT_thm2 = prove_thm
  (`UNLESS_STMT_thm2`,
   "!p q p' q' (st:*->*).
    ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
     (!s. ((p \/* p') UNLESS_STMT (q \/* q')) st s)",
    REWRITE_TAC [UNLESS_STMT;\/*] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                 (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THENL
      [
       RES_TAC THENL
         [
          ASM_REWRITE_TAC []
         ;
          ASM_REWRITE_TAC []
         ;
          ASM_REWRITE_TAC []
         ;
          ASM_REWRITE_TAC []
         ]
      ;
       RES_TAC THENL
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

%
  Conjunction Theorem:
               p unless_stmt Q in stmt, p' unless_stmt q' in stmt
     ------------------------------------------------------------------
     (p /\ p') unless_stmt (p /\ q') \/ (p' /\ q) \/ (q /\ q') in stmt
%
let UNLESS_STMT_thm3 = prove_thm
  (`UNLESS_STMT_thm3`,
   "!p q p' q' (st:*->*).
     ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
      (!s. ((p /\* p') UNLESS_STMT
           (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))) st s)",
    PURE_REWRITE_TAC [UNLESS_STMT;/\*;\/*] THEN 
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                 (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
    DISCH_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ASSUME_TAC (CONJUNCT1
         (ASSUME "(!s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s)) /\
                  (!s. p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))")) THEN
    ASSUME_TAC (CONJUNCT2
         (ASSUME "(!s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s)) /\
                  (!s. p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))")) THEN
    STRIP_ASSUME_TAC (SPEC_ALL
         (ASSUME "(!s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s))")) THEN
    STRIP_ASSUME_TAC (SPEC_ALL
         (ASSUME "(!s. p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))")) THEN
    ASSUME_TAC (UNDISCH_ALL
     (SPEC "(q':*->bool) ((st:*->*) s)" (SPEC "(p':*->bool) ((st:*->*) s)"
     (SPEC "(q':*->bool) s" (SPEC "(p':*->bool) s"
     (SPEC "(q:*->bool) ((st:*->*) s)" (SPEC "(p:*->bool) ((st:*->*) s)"
     (SPEC "(q:*->bool) s" (SPEC "(p:*->bool) s"
      IMP_IMP_CONJIMP_lemma))))))))) THEN
    ASM_REWRITE_TAC []);;

%
  Disjunction Theorem:

               p unless_stmt Q in stmt, p' unless_stmt q' in stmt
     ------------------------------------------------------------------
     (p \/ p') unless_stmt (~p /\ q') \/ (~p' /\ q) \/ (q /\ q') in stmt
%
let UNLESS_STMT_thm4 = prove_thm 
  (`UNLESS_STMT_thm4`,
   "!p q p' q' (st:*->*).
     ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
      (!s. ((p \/* p') UNLESS_STMT ((((~* p) /\* q') \/* ((~* p') /\* q)) \/* 
                                    (q /\* q'))) st s)",
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
       STRIP_TAC THEN STRIP_TAC THEN 
    PURE_REWRITE_TAC [UNLESS_STMT;/\*;\/*;~*] THEN 
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                    (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
    DISCH_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IMP_IMP_DISJIMP_lemma] THEN
    ASSUME_TAC (SPEC_ALL (CONJUNCT1
         (ASSUME "(!s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s)) /\
                  (!s. p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))"))) THEN
    ASSUME_TAC (SPEC_ALL (CONJUNCT2
         (ASSUME "(!s. p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s)) /\
                  (!s. p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))"))) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
  ["(p s /\ ~q s ==> p ((st:*->*) s) \/ q (st s))";
   "(p' s /\ ~q' s ==> p'((st:*->*) s) \/ q'(st s))"]
   AND_INTRO_THM)) THEN
    DISCH_TAC THEN
    ASSUME_TAC (UNDISCH_ALL
   (SPECL ["(p:*->bool) s";"(q:*->bool) s";
               "(p:*->bool) ((st:*->*)s)";"(q:*->bool) ((st:*->*)s)";
               "(p':*->bool) s";"(q':*->bool) s";
               "(p':*->bool) ((st:*->*)s)";"(q':*->bool) ((st:*->*)s)"]
               IMP_IMP_DISJIMP_lemma)) THEN
    ASM_REWRITE_TAC []);;

let UNLESS_STMT_thm5_lemma1 = TAC_PROOF
  (([],
   "!p q r. (p ==> q) ==> (p \/ r ==> q \/ r)"),
   REPEAT STRIP_TAC THENL
     [
      RES_TAC THEN ASM_REWRITE_TAC []
     ;
      ASM_REWRITE_TAC []]);;

let UNLESS_STMT_thm5_lemma2 = TAC_PROOF
  (([],
   "!(P:num->(*->bool)) q s. ((?n. P n s) \/ q s) = (?n. P n s \/ q s)"),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [
     EXISTS_TAC "n:num" THEN
     ASM_REWRITE_TAC []
    ;
     EXISTS_TAC "n:num" THEN
     ASM_REWRITE_TAC []
    ;
     DISJ1_TAC THEN
     EXISTS_TAC "n:num" THEN
     ASM_REWRITE_TAC []
    ;
     DISJ2_TAC THEN
     ASM_REWRITE_TAC []
    ]);;

let UNLESS_STMT_thm5 = prove_thm 
  (`UNLESS_STMT_thm5`,
   "!(P:num->(*->bool)) q st.
          (!m. (!s. ((P m) UNLESS_STMT q)st s)) ==>
               (!s. ((\s. ?n. P n s) UNLESS_STMT q)st s)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS_STMT] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [UNLESS_STMT_thm5_lemma2] THEN
   EXISTS_TAC "n:num" THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

%
 -----------------------------------------------------------------------------
  Theorems about UNLESS 
 -----------------------------------------------------------------------------
%

%
  The reflexivity theorem:

               p unless p in Prog
%
let UNLESS_thm1 = prove_thm 
  (`UNLESS_thm1`,
   "!(p:*->bool) Pr. (p UNLESS p) Pr",
   STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      PURE_REWRITE_TAC [UNLESS]
     ;
      GEN_TAC THEN
      PURE_REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
      CONJ_TAC THENL
        [
         GEN_TAC THEN
         PURE_REWRITE_TAC [BETA_CONV
           "(\s. (p:*->bool) s /\ ~p s ==> p (h s) \/ p (h s))s"] THEN
         REPEAT STRIP_TAC THEN
         RES_TAC
        ;
         PURE_ASM_REWRITE_TAC []
        ]
     ]);;

%
  The anti reflexivity theorem:

               p unless ~p in Prog
%
let UNLESS_thm2 = prove_thm 
  (`UNLESS_thm2`,
   "!(p:*->bool) Pr. (p UNLESS (~* p)) Pr",
   STRIP_TAC THEN LIST_INDUCT_TAC THENL
     [
      PURE_REWRITE_TAC[UNLESS]
     ;
      GEN_TAC THEN
      PURE_REWRITE_TAC [UNLESS;UNLESS_STMT;~*] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      ASM_REWRITE_TAC
        [GEN_ALL (SYM (SPEC_ALL ~*));NOT_CLAUSES;AND_CLAUSES;
         EXCLUDED_MIDDLE;IMP_CLAUSES]
     ]);;

%
  The unless implies theorem:

               p unless q in Pr, q ==> r
              ---------------------------
                   p unless r in Pr
%
let UNLESS_thm3 = prove_thm 
  (`UNLESS_thm3`,
   "!(p:*->bool) q r Pr.
      (((p UNLESS q) Pr) /\ (!s. (q s) ==> (r s))) ==> ((p UNLESS r) Pr)",
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THENL
      [
       REWRITE_TAC [UNLESS]
      ;
       X_GEN_TAC "st:*->*" THEN
       REWRITE_TAC [UNLESS] THEN
       REPEAT STRIP_TAC THENL
         [
          ASSUME_TAC (UNDISCH_ALL
            (SPECL ["(!s. ((p:*->bool) UNLESS_STMT q)st s)";
                    "(!s.  (q:*->bool) s ==> r s)"] AND_INTRO_THM)) THEN
          ASM_REWRITE_TAC [UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm1)]
         ;
          RES_TAC
         ]
      ]);;

%
  Conjunction Theorem:

               p unless q in Pr, p' unless q' in Pr
     -----------------------------------------------------------
     (p /\ p') unless (p /\ q') \/ (p' /\ q) \/ (q /\ q') in Pr
%
let UNLESS_thm4 = prove_thm
  (`UNLESS_thm4`,
   "!(p:*->bool) q p' q' Pr.
      (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
        (((p /\* p') UNLESS (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))) Pr)",
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      PURE_REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASSUME_TAC (UNDISCH_ALL (SPECL
            ["(!s. ((p:*->bool) UNLESS_STMT q)st s)";
             "(!s. ((p':*->bool) UNLESS_STMT q')st s)"]
             AND_INTRO_THM)) THEN
         ASM_REWRITE_TAC [UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm3)]
        ;
         RES_TAC
        ]
     ]);;

%
  Disjunction Theorem:

               p unless q in Pr, p' unless q' in Pr
     -------------------------------------------------------------
     (p \/ p') unless (~p /\ q') \/ (~p' /\ q) \/ (q /\ q') in Pr
%
let UNLESS_thm5 = prove_thm
  (`UNLESS_thm5`,
   "!(p:*->bool) q p' q' Pr.
      (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
          (((p \/* p') UNLESS ((((~* p) /\* q') \/* ((~* p') /\* q)) \/* 
                                     (q /\* q'))) Pr)",
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["!s:*. (p UNLESS_STMT q)st s";"!s:*. (p' UNLESS_STMT q')st s"]
            AND_INTRO_THM)) THEN
         ASM_REWRITE_TAC [UNDISCH_ALL (SPEC_ALL UNLESS_STMT_thm4)]
        ;
         RES_TAC
        ]
     ]);;

%
  Simple Conjunction Theorem:

               p unless q in Pr, p' unless_stmt q' in Pr
              -------------------------------------------
                    (p /\ p') unless (q \/ q') in Pr
%
let UNLESS_thm6 = prove_thm 
  (`UNLESS_thm6`,
   "!(p:*->bool) q p' q' Pr.
      (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
         (((p /\* p') UNLESS (q \/* q')) Pr)",
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) UNLESS q)Pr";"((p':*->bool) UNLESS q')Pr"]
          AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4)) THEN
    ASSUME_TAC (SPECL ["p:*->bool";"q:*->bool";"p':*->bool";"q':*->bool"]
                       IMPLY_WEAK_lemma1) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
       ["(((p:*->bool) /\* p') UNLESS
         (((p /\* q') \/* (p' /\* q)) \/* (q /\* q')))Pr";
        "!s. ((((p:*->bool) /\* q') \/* (p' /\* q)) \/* (q /\* q'))s ==>
                (q \/* q')s"]
        AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
         ["(p:*->bool) /\* p'";
          "((((p:*->bool) /\* q') \/* (p' /\* q)) \/* (q /\* q'))";
          "(q:*->bool) \/* q'";"Pr:(*->*)list"]
          UNLESS_thm3)]);;

%
  Simple Disjunction Theorem:

               p unless Q in Pr, p' unless q' in Pr
             ---------------------------------------
                 (p \/ p') unless (q \/ q') in Pr
%
let UNLESS_thm7 = prove_thm
  (`UNLESS_thm7`,
   "!(p:*->bool) q p' q' Pr.
         (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
             (((p \/* p') UNLESS (q \/* q')) Pr)",
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((p:*->bool) UNLESS q)Pr";"((p':*->bool) UNLESS q')Pr"]
         AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm5)) THEN
    ASSUME_TAC (SPECL ["p:*->bool";"q:*->bool";"p':*->bool";"q':*->bool"]
                       IMPLY_WEAK_lemma2) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         ["(((p:*->bool) \/* p') UNLESS
           ((((~* p) /\* q') \/* ((~* p') /\* q)) \/* (q /\* q'))) Pr";
          "!s. ((((~* (p:*->bool)) /\* q') \/* ((~* p') /\* q)) \/* 
                    (q /\* q'))s ==> (q \/* q')s"]
          AND_INTRO_THM)) THEN
    STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) \/* p')";
          "((((~* (p:*->bool)) /\* q') \/* ((~* p') /\* q)) \/* (q /\* q'))";
          "((q:*->bool) \/* q')";
          "Pr:(*->*)list"]
           UNLESS_thm3)));;

%
  Cancellation Theorem:

               p unless Q in Pr, q unless r in Pr
              ------------------------------------
                    (p \/ q) unless r in Pr
%
let UNLESS_thm8 = prove_thm
  (`UNLESS_thm8`,
   "!(p:*->bool) q r Pr.
     (((p UNLESS q) Pr) /\ ((q UNLESS r) Pr)) ==> (((p \/* q) UNLESS r) Pr)",
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) UNLESS q)Pr";"((q:*->bool) UNLESS r)Pr"]
          AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["p:*->bool";"q:*->bool";"q:*->bool";"r:*->bool"]
          UNLESS_thm5))) THEN
    ASSUME_TAC (SPECL
         ["p:*->bool";"q:*->bool";"r:*->bool"]
          IMPLY_WEAK_lemma3) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         ["(((p:*->bool) \/* q) UNLESS
           ((((~* p) /\* r) \/* ((~* q) /\* q)) \/* (q /\* r))) Pr";
          "!s:*. ((((~* p) /\* r) \/* ((~* q) /\* q)) \/* (q /\* r))s ==> r s"]
          AND_INTRO_THM)) THEN
    STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["((p:*->bool) \/* q)";
          "((((~* (p:*->bool)) /\* r) \/* ((~* q) /\* q)) \/* (q /\* r))";
          "r:*->bool"]
          UNLESS_thm3))));;

%
 -----------------------------------------------------------------------------
  Corollaries 
 -----------------------------------------------------------------------------
%

let UNLESS_cor1 = prove_thm
  (`UNLESS_cor1`,
   "!(p:*->bool) q Pr. (!s. p s ==> q s) ==> ((p UNLESS q) Pr)",
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
      ["((p:*->bool) UNLESS p)Pr";"!s:*. p s ==> q s"]
       AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
      ["p:*->bool";"p:*->bool";"q:*->bool";"Pr:(*->*)list"] UNLESS_thm3)]);;

let UNLESS_cor2 = prove_thm
  (`UNLESS_cor2`,
   "!(p:*->bool) q Pr. (!s. (~* p)s ==> q s) ==> ((p UNLESS q) Pr)",
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC_ALL UNLESS_thm2) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
      ["((p:*->bool) UNLESS (~* p))Pr";"!s:*. (~* p) s ==> q s"]
       AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
       ["p:*->bool";"~* (p:*->bool)";"q:*->bool";"Pr:(*->*)list"]
        UNLESS_thm3)]);;

let UNLESS_cor3a = TAC_PROOF
  (([],
   "!(p:*->bool) q r Pr.
          (p UNLESS (q \/* r)) Pr ==> ((p /\* (~* q)) UNLESS (q \/* r)) Pr"),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPECL ["~* (q:*->bool)";"Pr:(*->*)list"] UNLESS_thm2) THEN
   UNDISCH_TAC "((~* (q:*->bool)) UNLESS (~*(~* q)))Pr" THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) UNLESS (q \/* r))Pr";"((~* (q:*->bool)) UNLESS q)Pr"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["p:*->bool";"((q:*->bool) \/* r)";
      "(~* (q:*->bool))";"q:*->bool";"Pr:(*->*)list"]
      UNLESS_thm6)) THEN
   UNDISCH_TAC "(((p:*->bool) /\* (~* q)) UNLESS ((q \/* r) \/* q))Pr" THEN
   PURE_ONCE_REWRITE_TAC
      [SPECL ["(q:*->bool) \/* r";"q:*->bool"] OR_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_ASSOC_lemma))] THEN
   REWRITE_TAC [OR_OR_lemma]);;

let UNLESS_cor3b = TAC_PROOF
  (([],
   "!(p:*->bool) q r Pr.
      ((p /\* (~* q)) UNLESS (q \/* r)) Pr ==> (p UNLESS (q \/* r)) Pr"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL ["(p:*->bool) /\* q";"Pr:(*->*)list"] UNLESS_thm1) THEN
   ASSUME_TAC (SPECL ["p:*->bool";"q:*->bool"] AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["(((p:*->bool) /\* q) UNLESS (p /\* q))Pr";"!s:*. (p /\* q)s ==> q s"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["(p:*->bool) /\* q";"(p:*->bool) /\* q";"q:*->bool";"Pr:(*->*)list"]
      UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["(((p:*->bool) /\* (~* q)) UNLESS (q \/* r))Pr";
      "(((p:*->bool) /\* q) UNLESS q)Pr"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((p:*->bool) /\* (~* q))";"((q:*->bool) \/* r)";
      "((p:*->bool) /\* q)";"q:*->bool";"Pr:(*->*)list"]
      UNLESS_thm7)) THEN
   UNDISCH_TAC
   "((((p:*->bool) /\* (~* q)) \/* (p /\* q)) UNLESS ((q \/* r) \/* q))Pr" THEN
   REWRITE_TAC [AND_COMPL_OR_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL (OR_ASSOC_lemma)))] THEN
   REWRITE_TAC [OR_OR_lemma] THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor3 = prove_thm
  (`UNLESS_cor3`,
   "!(p:*->bool) q r Pr.
         ((p /\* (~* q)) UNLESS (q \/* r)) Pr = (p UNLESS (q \/* r)) Pr",
   REWRITE_TAC [IMP_ANTISYM_RULE
                 (SPEC_ALL UNLESS_cor3b) (SPEC_ALL UNLESS_cor3a)]);;

let UNLESS_cor4 = prove_thm
  (`UNLESS_cor4`,
   "!(p:*->bool) q r Pr.
               ((p \/* q) UNLESS r) Pr ==> (p UNLESS (q \/* r)) Pr",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL ((SPEC "~* (q:*->bool)" UNLESS_thm2))) THEN
   UNDISCH_TAC "((~* (q:*->bool)) UNLESS (~*(~* q)))Pr" THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["(((p:*->bool) \/* q) UNLESS r)Pr";"((~* (q:*->bool)) UNLESS q)Pr"]
          AND_INTRO_THM))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["((p:*->bool) \/* q)";"r:*->bool";"(~* (q:*->bool))";"q:*->bool"]
          UNLESS_thm6))) THEN
   UNDISCH_TAC "((((p:*->bool) \/* q) /\* (~* q)) UNLESS (r \/* q))Pr" THEN
   REWRITE_TAC [OR_NOT_AND_lemma] THEN
   PURE_ONCE_REWRITE_TAC [SPECL ["r:*->bool";"q:*->bool"] OR_COMM_lemma] THEN
   REWRITE_TAC [UNLESS_cor3] THEN
   STRIP_TAC THEN
   PURE_ONCE_REWRITE_TAC [SPECL ["r:*->bool";"q:*->bool"] OR_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor5 = prove_thm
  (`UNLESS_cor5`,
   "!(p:*->bool) Pr. (p UNLESS TRUE) Pr",
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm2) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) UNLESS p)Pr";"((p:*->bool) UNLESS (~* p))Pr"]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["p:*->bool";"p:*->bool";"p:*->bool";"(~* (p:*->bool))"]
          UNLESS_thm6))) THEN
   UNDISCH_TAC "(((p:*->bool) /\* p) UNLESS (p \/* (~* p)))Pr" THEN
   REWRITE_TAC [AND_AND_lemma;P_OR_NOT_P_lemma]);;

let UNLESS_cor6 = prove_thm
  (`UNLESS_cor6`,
   "!(p:*->bool) Pr. (TRUE UNLESS p) Pr",
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL (SPEC "(~* (p:*->bool))" UNLESS_thm2)) THEN
   UNDISCH_TAC "((~* (p:*->bool)) UNLESS (~*(~* p)))Pr" THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((~* (p:*->bool)) UNLESS p)Pr";"((p:*->bool) UNLESS p)Pr"]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["(~* (p:*->bool))";"p:*->bool";"p:*->bool";"p:*->bool"]
          UNLESS_thm7))) THEN
   UNDISCH_TAC "(((~* (p:*->bool)) \/* p) UNLESS (p \/* p))Pr" THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_OR_lemma;P_OR_NOT_P_lemma]);;

let UNLESS_cor7 = prove_thm
  (`UNLESS_cor7`,
   "!(p:*->bool) Pr. (FALSE UNLESS p) Pr",
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL (SPEC "(~* (p:*->bool))" UNLESS_thm2)) THEN
   UNDISCH_TAC "((~* (p:*->bool)) UNLESS (~*(~* p)))Pr" THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((~* (p:*->bool)) UNLESS p)Pr";"((p:*->bool) UNLESS p)Pr"]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         ["(~* (p:*->bool))";"p:*->bool";"p:*->bool";"p:*->bool"]
          UNLESS_thm6))) THEN
   UNDISCH_TAC "(((~* (p:*->bool)) /\* p) UNLESS (p \/* p))Pr" THEN
   PURE_ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [OR_OR_lemma;P_AND_NOT_P_lemma]);;

let HeJiFeng_lemma1 = TAC_PROOF
  (([],
   "!(p:*->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p s /\ ~q s ==> p' s /\ ~q s)"),
   REPEAT STRIP_TAC THENL [ASM_REWRITE_TAC [];RES_TAC]);;

let HeJiFeng_lemma2 = TAC_PROOF
  (([],
   "!(p:*->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p' s /\ ~q s ==> p s /\ ~q s)"),
   REPEAT STRIP_TAC THENL [ASM_REWRITE_TAC [];RES_TAC]);;

let HeJiFeng_lemma = TAC_PROOF
  (([],
   "!(p:*->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p s /\ ~q s = p' s /\ ~q s)"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [IMP_ANTISYM_RULE
     (SPEC_ALL (UNDISCH (UNDISCH (UNDISCH (SPEC_ALL HeJiFeng_lemma1)))))
     (SPEC_ALL (UNDISCH (UNDISCH (UNDISCH (SPEC_ALL HeJiFeng_lemma2)))))]);;

let HeJiFeng_lemma_f = MK_ABS (UNDISCH_ALL (SPEC_ALL HeJiFeng_lemma));;

let UNLESS_cor8 = prove_thm
  (`UNLESS_cor8`,
   "!(p:*->bool) q p' Pr.
       (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s)
            ==> (((p  /\* (~* q)) UNLESS q) Pr =
                 ((p' /\* (~* q)) UNLESS q) Pr)",
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [/\*;\/*;~*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [HeJiFeng_lemma_f]);;

%
  Corollary of generalized cancellation
%
let UNLESS_cor9 = prove_thm
  (`UNLESS_cor9`,
   "!(p:*->bool) q p' q' r r' Pr.
     ((p \/* p') UNLESS (q \/* r)) Pr /\ ((q \/* q') UNLESS (p \/* r')) Pr ==>
            ((p \/* p' \/* q \/* q') UNLESS ((p /\* q) \/* r \/* r')) Pr",
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) \/* p')";"((q:*->bool) \/* r)";
          "((q:*->bool) \/* q')";"((p:*->bool) \/* r')";"Pr:(*->*)list"]
          UNLESS_thm5)) THEN
   ASSUME_TAC (SPECL
        ["p:*->bool";"q:*->bool";"p':*->bool";"q':*->bool";
         "r:*->bool";"r':*->bool"] IMPLY_WEAK_lemma4) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      ["((((p:*->bool) \/* p') \/* (q \/* q')) UNLESS
        ((((~*(p \/* p')) /\* (p \/* r')) \/*
          ((~*(q \/* q')) /\* (q \/* r))) \/*
         ((q \/* r) /\* (p \/* r')))) Pr";
       "!s:*. ((((~*(p \/* p')) /\* (p \/* r')) \/*
              ((~*(q \/* q')) /\* (q \/* r))) \/*
              ((q \/* r) /\* (p \/* r'))) s ==>
                  ((p /\* q) \/* (r \/* r'))s"]
       AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
        ["(((p:*->bool) \/* p') \/* (q \/* q'))";
         "((((~*((p:*->bool) \/* p')) /\* (p \/* r')) \/*
          ((~*(q \/* q')) /\* (q \/* r))) \/*
          ((q \/* r) /\* (p \/* r')))";
         "(((p:*->bool) /\* q) \/* (r \/* r'))"]
         UNLESS_thm3))) THEN
   UNDISCH_TAC "((((p:*->bool) \/* p') \/* (q \/* q')) UNLESS
                ((p /\* q) \/* (r \/* r')))Pr" THEN
   REWRITE_TAC [OR_ASSOC_lemma]);;

let UNLESS_cor10 = prove_thm
  (`UNLESS_cor10`,
   "!(p:*->bool) q Pr. (p \/* q) STABLE Pr ==> (p UNLESS q) Pr",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
     ["p:*->bool";"q:*->bool";"FALSE:*->bool";"Pr:(*->*)list"]
      UNLESS_cor4)) THEN
   UNDISCH_TAC "((p:*->bool) UNLESS (q \/* FALSE))Pr" THEN
   REWRITE_TAC [OR_FALSE_lemma]);;

let UNLESS_cor11 = prove_thm
  (`UNLESS_cor11`,
   "!(p:*->bool) Pr. (!s. (~* p)s) ==> p STABLE Pr",
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
      DISCH_TAC THEN
      RES_TAC THEN
      ASM_REWRITE_TAC [FALSE_DEF] THEN
      UNDISCH_TAC "!s:*. ~* p s" THEN
      REWRITE_TAC [~*] THEN
      CONV_TAC (DEPTH_CONV BETA_CONV) THEN
      REPEAT STRIP_TAC THEN
      RES_TAC
     ]);;

let UNLESS_cor12 = prove_thm
  (`UNLESS_cor12`,
   "!(p:*->bool) Pr. (!s. (~* p)s) ==> (~* p) STABLE Pr",
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
      DISCH_TAC THEN
      RES_TAC THEN
      ASM_REWRITE_TAC [FALSE_DEF]
     ]);;

let UNLESS_cor13 = prove_thm
  (`UNLESS_cor13`,
   "!(p:*->bool) q Pr.
        (p UNLESS q) Pr /\ (q UNLESS p) Pr /\ (!s. ~* (p /\* q) s) ==>
                (p \/* q) STABLE Pr",
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         ["((p:*->bool) /\* q)";"Pr:(*->*)list"] UNLESS_cor11)) THEN
   UNDISCH_TAC "((p:*->bool) /\* q) STABLE Pr" THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      ["((p:*->bool) UNLESS q)Pr";"((q:*->bool) UNLESS p)Pr"]
       AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      ["(p:*->bool)";"(q:*->bool)";"(q:*->bool)";"(p:*->bool)";"Pr:(*->*)list"]
       UNLESS_thm5)) THEN
   UNDISCH_TAC "(((p:*->bool) \/* q) UNLESS
                ((((~* p) /\* p) \/* ((~* q) /\* q)) \/* (q /\* p))) Pr" THEN
   PURE_ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma;OR_FALSE_lemma] THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["(((q:*->bool) \/* p) UNLESS (p /\* q))Pr";
         "(((p:*->bool) /\* q) UNLESS FALSE)Pr"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["((q:*->bool) \/* p)";"((p:*->bool) /\* q)";
      "FALSE:*->bool";"Pr:(*->*)list"]
       UNLESS_thm8)) THEN
   UNDISCH_TAC "((((q:*->bool) \/* p) \/* (p /\* q)) UNLESS FALSE)Pr" THEN
   REWRITE_TAC [OR_AND_DISTR_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;OR_OR_lemma] THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;OR_OR_lemma;AND_AND_lemma]);;

let UNLESS_cor14 = prove_thm
  (`UNLESS_cor14`,
   "!(p:*->bool) q Pr. (p UNLESS (~* q)) Pr /\ q STABLE Pr ==>
                               (p UNLESS (p /\* (~* q))) Pr",
   REWRITE_TAC [STABLE] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    ["p:*->bool";"~* (q:*->bool)";"q:*->bool";"FALSE:*->bool";"Pr:(*->*)list"]
      UNLESS_thm4)) THEN
   UNDISCH_TAC "(((p:*->bool) /\* q) UNLESS
        (((p /\* FALSE) \/* (q /\* (~* q))) \/* ((~* q) /\* FALSE)))Pr" THEN
   REWRITE_TAC [AND_FALSE_lemma;P_AND_NOT_P_lemma;OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL
     ["(p:*->bool) /\* (~* q)";"Pr:(*->*)list"] UNLESS_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     ["(((p:*->bool) /\* q) UNLESS FALSE)Pr";
      "(((p:*->bool) /\* (~* q)) UNLESS (p /\* (~* q)))Pr"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL 
     ["(p:*->bool) /\* q";"FALSE:*->bool";
      "(p:*->bool) /\* (~* q)";"(p:*->bool) /\* (~* q)";"Pr:(*->*)list"]
      UNLESS_thm5)) THEN
   UNDISCH_TAC "((((p:*->bool) /\* q) \/* (p /\* (~* q))) UNLESS
                 ((((~*(p /\* q)) /\* (p /\* (~* q))) \/*
                   ((~*(p /\* (~* q))) /\* FALSE)) \/*
                    (FALSE /\* (p /\* (~* q)))))Pr" THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [AND_COMPL_OR_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [AND_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   REWRITE_TAC [NOT_AND_OR_NOT_lemma] THEN
   REWRITE_TAC [AND_OR_DISTR_lemma] THEN
   REWRITE_TAC [AND_ASSOC_lemma] THEN
   REWRITE_TAC [AND_AND_lemma] THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_OR_lemma] THEN
   REWRITE_TAC [AND_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor15_lem1 = TAC_PROOF
  (([],
   "!p q. p /\ (~p \/ ~q) = p /\ ~q"),
   REPEAT GEN_TAC THEN 
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN 
     (RES_TAC THEN ASM_REWRITE_TAC []));;

let UNLESS_cor15_lem2 = TAC_PROOF
  (([],
   "!p q. p \/ (p /\ q) = p"),
   REPEAT GEN_TAC THEN 
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN 
   ASM_REWRITE_TAC []);;

let UNLESS_cor15 = prove_thm
  (`UNLESS_cor15`,
   "!(P:num->(*->bool)) Q Pr.
       (!i. ((P i) UNLESS ((P i) /\* (Q i))) Pr) ==>
           (($!* P) UNLESS (($!* P) /\* ($?* Q))) Pr",
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      UNDISCH_TAC "(!i:num. (((P i):*->bool) UNLESS ((P i) /\* (Q i)))Pr) ==>
                   (($!* P) UNLESS (($!* P) /\* ($?* Q)))Pr" THEN
      REWRITE_TAC [!*;?*;UNLESS;UNLESS_STMT;/\*] THEN
      BETA_TAC THEN
      REWRITE_TAC [NOT_CLAUSES;AND_CLAUSES;OR_CLAUSES;DE_MORGAN_THM;
                   UNLESS_cor15_lem1] THEN
      REPEAT STRIP_TAC THENL
        [
         UNDISCH_TAC "~(?x:num. Q x (s:*))" THEN
         REWRITE_TAC [NOT_EXISTS_CONV "~(?x:num. Q x (s:*))"] THEN
         DISCH_TAC THEN
         DISJ1_TAC THEN
         GEN_TAC THEN
         ASSUME_TAC (SPEC_ALL (ASSUME "!x:num. P x (s:*)")) THEN
         ASSUME_TAC (SPEC_ALL (ASSUME "!x:num. ~Q x (s:*)")) THEN
         ASSUME_TAC (UNDISCH_ALL (SPECL
           ["(P:num->(*->bool)) x s";"~(Q:num->(*->bool)) x s"]
            AND_INTRO_THM)) THEN
         ASSUME_TAC (UNDISCH (SPEC "s:*" (CONJUNCT1 (SPEC "x:num" (ASSUME
           "!i:num. (!s:*. P i s /\ ~Q i s ==>
                         P i(st s) \/ P i(st s) /\ Q i(st s)) /\
                         ((P i) UNLESS (\s. P i s /\ Q i s))Pr"))))) THEN
         UNDISCH_TAC
           "(P:num->(*->bool)) x((st:*->*) s) \/ P x(st s) /\ Q x(st s)" THEN
         REWRITE_TAC [UNLESS_cor15_lem2]
        ;
         ASSUME_TAC (GEN_ALL (CONJUNCT2 (SPEC "x:num" (ASSUME
           "!i:num. (!s:*.
                P i s /\ ~Q i s ==> P i(st s) \/ P i(st s) /\ Q i(st s)) /\
               ((P i) UNLESS (\s. P i s /\ Q i s))Pr")))) THEN
         RES_TAC
        ]
     ]);;

let UNLESS_cor16 = prove_thm
  (`UNLESS_cor16`,
   "!(P:num->(*->bool)) Q Pr.
    (!i. ((P i) UNLESS (Q i))Pr) ==> (!i. ((/<=\* P i) UNLESS (\<=/* Q i))Pr)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   INDUCT_TAC THENL
     [
      ASM_REWRITE_TAC [/<=\*;\<=/* ]
     ;
      REWRITE_TAC [/<=\*;\<=/* ] THEN
      ASSUME_TAC (SPEC "SUC i" (ASSUME
        "!i. (((P:num->(*->bool)) i) UNLESS (Q i))Pr")) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL
        ["/<=\* (P:num->(*->bool)) i";"\<=/* (Q:num->(*->bool)) i";
         "(P:num->(*->bool))(SUC i)";"(Q:num->(*->bool))(SUC i)";
         "Pr:(*->*)list"]
         UNLESS_thm6))))
     ]);;

let UNLESS_cor17 = prove_thm
  (`UNLESS_cor17`,
   "!(P:num->(*->bool)) q Pr.
       (!i. ((P i) UNLESS q)Pr) ==> (!i. ((/<=\* P i) UNLESS q)Pr)",
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   INDUCT_TAC THENL
     [
      ASM_REWRITE_TAC [/<=\*;\<=/* ]
     ;
      REWRITE_TAC [/<=\*;\<=/* ] THEN
      ASSUME_TAC (SPEC "SUC i" (ASSUME
        "!i. (((P:num->(*->bool)) i) UNLESS q)Pr")) THEN
      ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL
        ["/<=\* (P:num->(*->bool)) i";"q:*->bool";
         "(P:num->(*->bool))(SUC i)";"q:*->bool";"Pr:(*->*)list"]
         UNLESS_thm6)))) THEN
      UNDISCH_ONE_TAC THEN
      REWRITE_TAC [OR_OR_lemma]
     ]);;

let UNLESS_cor18 = prove_thm
  (`UNLESS_cor18`,
   "!(P:num->(*->bool)) q Pr.
        (!m. ((P m) UNLESS q) Pr) ==> (($?* P) UNLESS q) Pr",
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS]
     ;
      X_GEN_TAC "st:*->*" THEN
      REWRITE_TAC [UNLESS;?*] THEN
      REPEAT STRIP_TAC THENL
        [
         STRIP_ASSUME_TAC (SPEC "s:*" (MP (SPEC_ALL UNLESS_STMT_thm5)
          (GEN "m:num" (CONJUNCT1 (SPEC "m:num" (ASSUME
            "!m:num. (!s:*. ((P m) UNLESS_STMT q) st s) /\
                            ((P m) UNLESS q) Pr"))))))
        ;
         STRIP_ASSUME_TAC (REWRITE_RULE [?*] (MP
          (ASSUME
            "(!m. (((P:num->*->bool) m) UNLESS q)Pr) ==> (($?* P) UNLESS q)Pr")
          (GEN "m:num" (CONJUNCT2 (SPEC "m:num" (ASSUME
            "!m:num. (!s:*. ((P m) UNLESS_STMT q) st s) /\
                            ((P m) UNLESS q) Pr"))))))
        ]
     ]);;

let UNLESS_cor19 = prove_thm
  (`UNLESS_cor19`,
   "!Pr. (FALSE:*->bool) STABLE Pr",
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REWRITE_TAC [UNLESS_thm1]);;

let UNLESS_cor20 = prove_thm
  (`UNLESS_cor20`,
   "!(p:*->bool) q Pr.
        (p STABLE Pr) /\ (q STABLE Pr) ==> ((p /\* q) STABLE Pr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma] (SPECL
     ["p:*->bool";"FALSE:*->bool";"q:*->bool";"FALSE:*->bool";
      "Pr:(*->*)list"] UNLESS_thm4)));;

let UNLESS_cor21 = prove_thm
  (`UNLESS_cor21`,
   "!(p:*->bool) q Pr.
        (p STABLE Pr) /\ (q STABLE Pr) ==> ((p \/* q) STABLE Pr)",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma] (SPECL
     ["p:*->bool";"FALSE:*->bool";"q:*->bool";"FALSE:*->bool";
      "Pr:(*->*)list"] UNLESS_thm7)));;

let UNLESS_cor22 = prove_thm
  (`UNLESS_cor22`,
   "!(p:*->bool) q r Pr.
        (p UNLESS q) Pr /\ (r STABLE Pr) ==> ((p /\* r) UNLESS (q /\* r))Pr",
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [OR_FALSE_lemma] (ONCE_REWRITE_RULE [OR_COMM_lemma]
    (ONCE_REWRITE_RULE [OR_AND_COMM_lemma]
      (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma] (SPECL
        ["p:*->bool";"q:*->bool";"r:*->bool";"FALSE:*->bool";
         "Pr:(*->*)list"] UNLESS_thm4))))));;

close_theory();;
