% -*- Emacs Mode: fundamental -*- %


%------------------------------------------------------------------------------

   File:         mk_example01.ml

   Author:       (c) Copyright Flemming Andersen 1990
   Date:         January 9, 1990

   Description:  

     This example was taken from the book:

	Parallel Program Design, A Foundation
	K. Mani Chandy & Jayadev Misra
	Page 168 - 170.

     The example is a simple specification of the dining philosophers and
     intends to illustrate how one may compose two specifications and derive
     properties of the composed system.

------------------------------------------------------------------------------%

system `/bin/rm example01.th`;;

loadt`l_unity`;;

new_theory`example01`;;

%
  INTRODUCTION.

  To make the specification taken from the Chandy Misra book, we must define
  a state having the properties as described. In the example the state of the
  system is informally given as a set of variables, every variable representing
  a dining philosopher. A philosophers activity may be asked by the predicates
  u.t, u.h and u.e.

  To reflect this description in our HOL example, a philosopher can be doing
  one of three possible things, defined by the type:

	dine = 	EATING | THINKING | HUNGRY.

  A state of philosopher activities may then be represented as a function from
  some unspecified type of the philosopher to the dine type representing the
  actual activity in a given state:

	s:*->dine.

  To ask for the activity of a philosopher in a given state, we introduce three
  predicates:

	eating, thinking and hungry.

  Every predicate take a philosopher as argument and returns a state abstracted
  boolean value as result, expressing whether the predicate, say eating, is
  satisfied for philosopher p in any state s. This is written as:

        eating p.

  In this way we abstract the predicates u.e, u.t and u.h as described in the
  book. The quantification is made over all philosophers p.
%

%
  Defining the type dine:
%
let dine_Axiom = define_type `dine_Axiom` `dine = EATING | THINKING | HUNGRY`;;

%
  To prove some properties of this type we need an induction theorem for
  the dine type:
%
let dine_Induct = prove_induction_thm dine_Axiom;;

%
  Make the induction theorem a tactic:
%
let dine_INDUCT_TAC = INDUCT_THEN dine_Induct ASSUME_TAC;;

%
  To prove the needed properties, we must have some additionally information
  about the type:
%
let exists_dine_thm1 = prove_rec_fn_exists dine_Axiom 
      "(f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)";;

let exists_dine_thm2 = prove_rec_fn_exists dine_Axiom 
      "(f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)";;

%
  Now we are able to prove some trivial theorems about the type dine, which
  are needed to prove the used equalities in the example:
%
let dine_thm1 = TAC_PROOF
  (([], "~(EATING = THINKING)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC "?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm2 = TAC_PROOF
  (([], "~(THINKING = EATING)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC "?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm3 = TAC_PROOF
  (([], "~(EATING = HUNGRY)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC "?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm4 = TAC_PROOF
  (([], "~(HUNGRY = EATING)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm1 THEN
   UNDISCH_TAC "?f. (f EATING = T) /\ (f THINKING = F) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm5 = TAC_PROOF
  (([], "~(THINKING = HUNGRY)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm2 THEN
   UNDISCH_TAC "?f. (f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm6 = TAC_PROOF
  (([], "~(HUNGRY = THINKING)"),
   DISCH_TAC THEN
   ASSUME_TAC exists_dine_thm2 THEN
   UNDISCH_TAC "?f. (f EATING = F) /\ (f THINKING = T) /\ (f HUNGRY = F)" THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let dine_thm7 = TAC_PROOF
  (([], "!u:dine. ~(u = EATING) = ((u = THINKING) \/ (u = HUNGRY))"),
   dine_INDUCT_TAC THENL
     [REWRITE_TAC [DE_MORGAN_THM;dine_thm1;dine_thm3];
      REWRITE_TAC [DE_MORGAN_THM;dine_thm2;dine_thm4];
      REWRITE_TAC [DE_MORGAN_THM;dine_thm4]]);;

%
  Now we define the state predicates for expressing the activity of
  philosophers:
%
let eating = new_definition
   (`eating`,
    "eating (p:*) = (\s:*->dine. (s p) = EATING)");;

let thinking = new_definition
   (`thinking`,
    "thinking (p:*) = (\s:*->dine. (s p) = THINKING)");;

let hungry = new_definition
   (`hungry`,
    "hungry (p:*) = (\s:*->dine. (s p) = HUNGRY)");;


%
  Proving the used equalities:
%
let dine_thm8 = GEN "p:*" (GEN "s:*->dine" (SPEC "(s:*->dine) p" dine_thm7));;

%
  Proving the used equality:
	~eating p = thinking p \/ hungry p
%
let dine_thm9 = TAC_PROOF
  (([], "!p:*. (~* (eating p)) = ((thinking p) \/* (hungry p))"),
   REWRITE_TAC [eating;thinking;hungry] THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC "p:*" dine_thm8)));;

let dine_thm10 = TAC_PROOF
  (([], "!u:dine. ~(u = THINKING) = ((u = HUNGRY) \/ (u = EATING))"),
   dine_INDUCT_TAC THENL
     [REWRITE_TAC [DE_MORGAN_THM;dine_thm1;dine_thm3];
      REWRITE_TAC [DE_MORGAN_THM;dine_thm2;dine_thm4;dine_thm5];
      REWRITE_TAC [DE_MORGAN_THM;dine_thm3;dine_thm5;dine_thm6]]);;

let dine_thm11 = GEN "p:*" (GEN "s:*->dine" (SPEC "(s:*->dine)p" dine_thm10));;

%
  Proving the used equality:
	~thinking p = hungry p \/ eating p
%
let dine_thm12 = TAC_PROOF
  (([], "!p:*. (~* (thinking p)) = ((hungry p) \/* (eating p))"),
   REWRITE_TAC [eating;thinking;hungry] THEN
   REWRITE_TAC [~*;\/*] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC "p:*" dine_thm11)));;

%
  The Specification.
  ==================

  The method used here is an attempt to bind properties to a certain component.
  This way of specifying may be changed if a better idea turns up.
%

%
  Properties given for the user component:
                           ===============
%
let user_safe1 = new_definition (`user_safe1`,
   "user_safe1 user = !p:*. ((thinking p) UNLESS (hungry p)) user");;

let user_safe2 = new_definition (`user_safe2`,
   "user_safe2 user = !p:*. (hungry p) STABLE user");;

let user_safe3 = new_definition (`user_safe3`,
   "user_safe3 user = !p:*. ((eating p) UNLESS (thinking p)) user");;

%
  Properties given for the G component:
                           ============
%
let G_safe1    =  new_definition (`G_safe1`,
   "G_safe1 G = !p:*. (thinking p) STABLE G");;

let G_safe2    =  new_definition (`G_safe2`,
   "G_safe2 G = !p:*. (~*(thinking p)) STABLE G");;

let G_safe3    =  new_definition
  (`G_safe3`, "G_safe3 G = !p:*. (eating p) STABLE G");;

let G_safe4    =  new_definition
  (`G_safe4`, "G_safe4 G = !p:*. (~* (eating p)) STABLE G");;

%
  Conditional Properties:
%
let G_cond =  new_definition (`G_cond`,
   "G_cond G init_cond = !(pi:*) pj. ~(pi = pj) ==>
                (~*((eating pi) /\* (eating pj))) INVARIANT (init_cond, G)");;

let user_live1 = new_definition (`user_live1`,
   "user_live1 user init_cond =
      !(p:*) (G:((*->dine)->(*->dine))list).
          G_cond G init_cond ==> ((eating p) LEADSTO (thinking p)) user");;

%
  Properties for the composed system mutex:
                     ======================
%

%
  Is this the right way of specifying the mutual exclusion property?
%
let mutex_safe1 = new_definition (`mutex_safe1`,
   "mutex_safe1 G user init_cond =
    !(pi:*) pj. ~(pi = pj) ==>
    (~*((eating pi) /\* (eating pj))) INVARIANT(init_cond, (APPEND user G))");;

let mutex_live1 = new_definition (`mutex_live1`,
   "mutex_live1 G user =
      !p:*. ((hungry p) LEADSTO (eating p)) (APPEND user G)");;

%------------------------------------------------------------------------------
*									      *
*			Derived properties				      *
*									      *
------------------------------------------------------------------------------%

%
  Due to restricted use of SPEC, SPECL, the type instantiation is needed.
  Strange since REWRITE tactics do not need the instantiation
%
let UNLESS_thm8     = INST_TYPE [(":*->dine",":*")] UNLESS_thm8;;
let FALSE_DEF       = INST_TYPE [(":*->dine",":*")] FALSE_DEF;;
let COMP_UNITY_cor2 = INST_TYPE [(":*->dine",":*")] COMP_UNITY_cor2;;
let UNLESS_thm2     = INST_TYPE [(":*->dine",":*")] UNLESS_thm2;;
let UNLESS_thm4     = INST_TYPE [(":*->dine",":*")] UNLESS_thm4;;
let OR_COMM_lemma   = INST_TYPE [(":*->dine",":*")] OR_COMM_lemma;;
let AND_OR_DISTR_lemma   = INST_TYPE [(":*->dine",":*")] AND_OR_DISTR_lemma;;
let UNLESS_thm3     = INST_TYPE [(":*->dine",":*")] UNLESS_thm3;;
let AND_COMM_lemma   = INST_TYPE [(":*->dine",":*")] AND_COMM_lemma;;
let SYM_AND_IMPLY_WEAK_lemma = INST_TYPE [(":*->dine",":*")]
    SYM_AND_IMPLY_WEAK_lemma;;

%
  Derived property:

     Given properties user_safe1, user_safe2, user_safe3, prove that all users
     satisfy:

	!user p. user_safe1 user /\ user_safe2 user /\ user_safe3 user ==>
            ~eating p is stable in user
%
let user_thm1 = TAC_PROOF
  (([], "!user (p:*).
           user_safe1 user /\ user_safe2 user /\ user_safe3 user ==>
               (~* (eating p)) STABLE user"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [user_safe1;user_safe2;user_safe3] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC "p:*" (ASSUME "!p:*. (hungry p) STABLE user")) THEN
   ASSUME_TAC
       (SPEC "p:*" (ASSUME "!p:*. ((thinking p) UNLESS (hungry p)) user")) THEN
   UNDISCH_TAC "(hungry (p:*)) STABLE user" THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((thinking (p:*)) UNLESS (hungry p))user";
         "((hungry (p:*)) UNLESS FALSE)user"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["thinking (p:*)";"hungry (p:*)";
         "FALSE:(*->dine)->bool";"user:((*->dine)->(*->dine))list"]
         UNLESS_thm8)) THEN
   UNDISCH_TAC "(((thinking (p:*)) \/* (hungry p)) UNLESS FALSE)user" THEN
   REWRITE_TAC [SYM (SPEC_ALL dine_thm9)]);;

%
  Derived property:

     Given properties user_safe1 and G_safe1, prove that all users and Gs
     satisfy:

	!user G p. user_safe1 user /\ G_safe1 G ==>
            (thinking p) unless (hungry p) in (user [] G)

     in the composed system mutex.
%
let mutex_thm1 = TAC_PROOF
  (([], "!user G (p:*). user_safe1 user /\ G_safe1 G ==>
               ((thinking p) UNLESS (hungry p)) (APPEND user G)"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [user_safe1;G_safe1] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
        "!p:*. ((thinking p) UNLESS (hungry p))user")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!p:*. (thinking p) STABLE G")) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
       ["((thinking (p:*)) UNLESS (hungry p))user";
        "(thinking (p:*)) STABLE G"]
        AND_INTRO_THM)) THEN
   REWRITE_TAC [UNDISCH_ALL (SPECL
       ["thinking (p:*)";"hungry (p:*)";"user:((*->dine)->(*->dine))list";
        "G:((*->dine)->(*->dine))list"] COMP_UNITY_cor2)]);;

%
  Derived property:

     Given properties user_safe2 and G_safe2, prove that all users and Gs
     satisfy:

	!user G p. user_safe2 user /\ G_safe2 G ==>
            (hungry p) unless (eating p) in (user [] G)

     in the composed system mutex.

  The rewriting of boolean expressions are tedious, need to invent something
  better.
%
let mutex_thm2 = TAC_PROOF
  (([], "!(p:*) user G. user_safe2 user /\ G_safe2 G ==>
                     ((hungry p) UNLESS (eating p)) (APPEND G user)"),
   REWRITE_TAC [user_safe2;G_safe2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!p:*. (~*(thinking p)) STABLE G")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!p:*. (hungry p) STABLE user")) THEN
   UNDISCH_TAC "(~*(thinking (p:*))) STABLE G" THEN
   REWRITE_TAC [dine_thm12] THEN
   ASSUME_TAC (SPECL
        ["hungry (p:*)";"G:((*->dine)->(*->dine))list"] UNLESS_thm2) THEN
   REWRITE_TAC [STABLE] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((hungry (p:*)) UNLESS (~*(hungry p)))G";
         "(((eating (p:*)) \/* (hungry p)) UNLESS FALSE)G"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["hungry (p:*)";"~* (hungry (p:*))";
         "(eating (p:*)) \/* (hungry p)";"FALSE:(*->dine)->bool";
         "G:((*->dine)->(*->dine))list"] UNLESS_thm4)) THEN
   UNDISCH_TAC
         "(((hungry p) /\* ((eating p) \/* (hungry p))) UNLESS
           ((((hungry (p:*)) /\* FALSE) \/*
            (((eating p) \/* (hungry p)) /\* (~*(hungry p)))) \/*
           ((~*(hungry p)) /\* FALSE))) G" THEN
   REWRITE_TAC [AND_FALSE_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        ["FALSE:(*->dine)->bool";
         "((eating (p:*)) \/* (hungry p)) /\* (~*(hungry p))"]
         OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        ["hungry (p:*)";"eating (p:*)";"hungry (p:*)"]
         AND_OR_DISTR_lemma] THEN
   REWRITE_TAC [AND_AND_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        ["hungry (p:*)";"eating (p:*)"] AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_Q_OR_Q_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [SPECL
        ["~* (hungry (p:*))";"eating (p:*)";"hungry (p:*)"]
         AND_OR_DISTR_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL
        ["eating (p:*)";"~* (hungry (p:*))"]
         SYM_AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((hungry (p:*)) UNLESS ((eating p) /\* (~*(hungry p))))G";
         "!s:*->dine. ((eating p) /\* (~*(hungry p)))s ==> eating p s"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["hungry (p:*)";"(eating (p:*)) /\* (~*(hungry p))";
         "eating (p:*)";"G:((*->dine)->(*->dine))list"]
         UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((hungry (p:*)) UNLESS (eating p))G";
         "(hungry (p:*)) STABLE user"]
         AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
        ["hungry (p:*)";"eating (p:*)";"G:((*->dine)->(*->dine))list";
         "user:((*->dine)->(*->dine))list"] COMP_UNITY_cor2)));;

%
  Derived property:

     Given properties user_safe3 and G_safe3, prove that all users and Gs
     satisfy:

	!user G p. user_safe3 user /\ G_safe3 G ==>
            (eating p) unless (thinking p) in (user [] G)

     in the composed system mutex.
%
let mutex_thm3 = TAC_PROOF
  (([], "!user G (p:*). user_safe3 user /\ G_safe3 G ==>
                  ((eating p) UNLESS (thinking p)) (APPEND user G)"),
   REWRITE_TAC [user_safe3;G_safe3] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!p:*. (eating p) STABLE G")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME
        "!p:*. ((eating p) UNLESS (thinking p))user")) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        ["((eating (p:*)) UNLESS (thinking p))user";
         "(eating (p:*)) STABLE G"]
         AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
        ["eating (p:*)";"thinking (p:*)";"user:((*->dine)->(*->dine))list";
         "G:((*->dine)->(*->dine))list"] COMP_UNITY_cor2)));;

%
  End of example
%

close_theory();;
