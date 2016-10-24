% -*- Emacs Mode: fundamental -*- %


%------------------------------------------------------------------------------

   File:         mk_example03.ml

   Author:       (c) Copyright Flemming Andersen 1990
   Date:         January 25, 1990

   Description:  

   The purpose of this example has been to make a complete specification with
   both program and property specification. We prove that assuming the
   environment satisfying certain safety and progress properties, then all the
   properties needed and wanted for the program implementing the 2-Arbiter
   protocol is satisfied as given by the specified properties.


   The 2-Arbiter example in this file was originally developed by

	   Joergen Staunstrup and Hans Henrik Loevengreen
	   Department of Computer Science,
	   Technical University of Denmark

   for teaching students at the university in using UNITY.

   Some proofs missing in the original example have been added in this version
   to complete the verification of the 2-Arbiter program.


   PS. If I was to make this example again, several details would be different,
       but I still believe it is useful as an example of using the HOL-UNITY
       system.

------------------------------------------------------------------------------%



%*****************************************************************************%
%
   Description of the example:


   We want to specify a 2-ARBITER as the composition of an arbiter (Arb) and
   some users (User) of the arbiter.

   The entire system (System) is then the composition of the two components:

      System = (Arb U User)

   We may graphically describe the composed system by:

    ---------------------------------------------------------------
    |                                                             |
    | System                                                      |
    |                                                             |
    |       ------------------------------------------------      |
    |      |                                                |     |
    |      |                    Arb                         |     |
    |      |                                                |     |
    |      |     --------  -------    --------  -------     |     |
    |       -----|      |--|     |----|      |  |     |-----      |
    |            | req1 |--| gr1 |----| req2 |--| gr2 |           |
    |       -----|      |--|     |----|      |  |     |-----      |
    |      |     --------  -------    --------  -------     |     |
    |      |                                                |     |
    |      |                  Users                         |     |
    |      |                                                |     |
    |       ------------------------------------------------      |
    |                                                             |
    |                                                             |
    ---------------------------------------------------------------


    The task of the Arb component is to ensure exclusive access to one of
    possibly two users, who wants to get access to a shared resource, and
    the Arb component must guarantee grant (gri) on request (reqi). However
    we only require the Arb component to satisfy these demands if the users
    (User) of the arbiter behaves in a nice manner as described below.


  Specification of System:
  ------------------------

  The 2 arbiter must satisfy the following properties:


  The initial condition of the system is given by:

         IC = ~req1 /\ ~req2 /\ ~gr1 /\ ~gr2                        (IC)


  Unconditional properties given for the Arbiter component:
                                         ==================

         ~(gr1 /\ gr2) INVARIANT IN (IC, Arb)                       (A1)

         !i.  reqi STABLE IN Arb                                    (A2)

         !i. ~reqi STABLE IN Arb                                    (A3)

         !i.  gri  UNLESS ~reqi IN Arb                              (A4)


  Unconditional properties given for the User component:
                                         ===============
         !i.  gri  STABLE IN User                                   (U1)

         !i. ~gri  STABLE IN User                                   (U2)

         !i.  reqi UNLESS  gri IN User                              (U3)

         !i. ~reqi UNLESS ~gri IN User                              (U4)


  Conditional properties given for the Arbiter component:
                                       ==================

         !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\                   (CA1)
                  gri LEADSTO ~reqi IN (Arb U User)
                      ==> reqi LEADSTO gri IN (Arb U User)

         !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\                   (CA2)
                  gri LEADSTO ~reqi IN (Arb U User)
                      ==> gri /\ ~reqi LEADSTO ~gri IN (Arb U User)


  Conditional properties given for the User component:
                                       ===============

         !i Arb. (A1) /\ (A2) /\ (A3) /\ (A4) /\                   (CU1)
                 ~(gr1 /\ gr2) INVARIANT IN (IC, (Arb U User))
                      ==> gri LEADSTO ~reqi IN (Arb U User)



  An Arbiter Program:
  -------------------

  We claim (and later prove) that the following 2-arbiter program satisfies the
  specified properties as given above


  program arb_prog;

    initially !i. reqi = gri = FALSE;

  begin

       req1      := TRUE                if req1 /\ ~gr2           (grantleft)
   []
       req2      := TRUE                if ~req1 /\ ~gr1 /\ req2  (grantright)
   []
       gr1, gr2  := FALSE, req2         if ~req1 /\ gr1           (doneleft)
   []
       gr2      := FALSE               if ~req2 /\ gr2           (doneright)

  end;



  Verifying that the Arb program Satisfies the Specification:
  -----------------------------------------------------------

  The following proofs was first made as ordinary UNITY proofs by hand. In this
  file you will only find proofs as HOL-UNITY proofs, and some comments on
  how the proving is done.


  We want to prove that the given program arb_prog satisfies the specification
  such that assuming the required behavior of the users (User) we may conclude
  that a request (reqi) leads to a satisfied grant (gri). We may write the
  wanted property as:

      !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
          !i. gri LEADSTO ~reqi IN (arb_prog U User)
              ==> !i. reqi LEADSTO gri IN (arb_prog U User)

  To prove this we may start by proving some additional properties of the
  composed system (Arb U User) given the specification above.

    mutex_thm0 =
      !User Arb. (U2) /\ (A1) ==> ~(gr1 /\ gr2) INVARIANT (IC, (Arb U User))

    mutex_thm1 =
      !i User Arb.
         (U1) /\ (U2) /\ (U3) /\ (U4) /\ (CU1) /\
         (A1) /\ (A2) /\ (A3) /\ (A4) /\ (CA1)
             ==> reqi LEADSTO gri IN (Arb U User)

    mutex_thm2 =
      !i User Arb.
         (U1) /\ (U2) /\ (U3) /\ (U4) /\ (CU1) /\
         (A1) /\ (A2) /\ (A3) /\ (A4) /\ (CA1)
             ==> gri LEADSTO ~reqi IN (Arb U User)

    mutex_thm3 =
      !i User Arb.
         (U1) /\ (U2) /\ (U3) /\ (U4) /\ (CU1) /\
         (A1) /\ (A2) /\ (A3) /\ (A4) /\ (CA1)
             ==> reqi LEADSTO ~reqi IN (Arb U User)

    mutex_thm4 =
      !i User Arb.
         (U1) /\ (U2) /\ (U3) /\ (U4) /\ (CU1) /\
         (A1) /\ (A2) /\ (A3) /\ (A4) /\ (CA2)
             ==> gri /\ ~reqi LEADSTO ~gri IN (Arb U User)


  We now want to prove that the arb_prog program satisfies the following
  properties:

    Proof obligations:

      We need to prove that the Arb program satisfies the specified properties
      (A1), (A2), (A3), (A4):

    arb_safe1_thm =                                       (A1)
       ~(gr1 /\ gr2) INVARIANT (IC, arb_prog)

    arb_safe2_thm =                                       (A2)
       !i. reqi STABLE IN arb_prog

    arb_safe3_thm =                                       (A3)
       !i. ~reqi STABLE IN arb_prog

    arb_safe4_thm =                                       (A4)
       !i. gri UNLESS ~reqi IN arb_prog


  We may prove some additional properties of arb_prog which are needed for
  proving the wanted progress property (LEADSTO) of the composed system:

    arb_safe_tr1_thm =
       req1 /\ ~gr2 UNLESS gr1 /\ req1 /\ ~gr2 IN arb_prog

    arb_safe_tr2_thm =
       req2 /\ ~req1 /\ ~gr1 UNLESS gr2 /\ req2 /\ ~req1 /\ ~gr1 IN arb_prog

    arb_safe_tr3_thm =
      ~req1 /\  gr1 UNLESS
      ~gr1 /\ gr2 /\ req2 \/ ~gr2 /\ ~req2 /\ ~req1 IN arb_prog

    arb_safe_tr4_thm =
       ~req2 /\ gr2 UNLESS ~gr2 /\ ~req2 IN arb_prog

    arb_live_tr1_thm =
       req1 /\ ~gr2 ENSURES gr1 /\ req1 /\ ~gr2 IN arb_prog

    arb_live_tr2_thm =
       req2 /\ ~req1 /\ ~gr1 ENSURES gr2 /\ req2 /\ ~req1 /\ ~gr1 IN arb_prog

    arb_live_tr3_thm =
      ~req1 /\ gr1 ENSURES
      ~gr1 /\ gr2 /\ req2 \/ ~gr2 /\ ~req2 /\ ~req1 IN arb_prog

    arb_live_tr4_thm =
       ~req2 /\ gr2 ENSURES ~gr2 /\ ~req2 IN arb_prog

    arb_safe_tr2a_thm =
       req2 /\ ~req1 /\ gr1 UNLESS gr2 IN arb_prog

    arb_live_tr2a_thm =
       req2 /\ ~req1 /\ gr1 ENSURES gr2 IN arb_prog

    arb_safe_tr1a_thm =
       req1 /\ ~gr1 /\ req2 /\ ~gr2 UNLESS gr1 /\ req2 IN arb_prog

    arb_live_tr1a_thm =
       req1 /\ ~gr1 /\ req2 /\ ~gr2 ENSURES gr1 /\ req2 IN arb_prog

    arb_safe_tr2b_thm =
       ~req1 /\ ~gr1 /\ req2 /\ ~gr2 UNLESS gr2 IN arb_prog

    arb_live_tr2b_thm =
       ~req1 /\ ~gr1 /\ req2 /\ ~gr2 ENSURES gr2 IN arb_prog

    arb_safe_tr1b_thm =
       req1 /\ ~gr2 UNLESS gr1 IN arb_prog

    arb_live_tr1b_thm =
       req1 /\ ~gr2 ENSURES gr1 IN arb_prog

    arb_safe_tr1c_thm =
       req1 /\ ~gr1 /\ ~gr2 UNLESS gr1 IN arb_prog

    arb_live_tr1c_thm =
       req1 /\ ~gr1 /\ ~gr2 ENSURES gr1 IN arb_prog

    arb_safe_tr4a_thm =
       req1 /\ ~gr1 /\ ~ req2 /\ gr2 UNLESS req1 /\ ~gr1 /\ ~gr2 IN arb_prog

    arb_live_tr4a_thm =
       req1 /\ ~gr1 /\ ~ req2 /\ gr2 ENSURES req1 /\ ~gr1 /\ ~gr2 IN arb_prog

  from these proofs and the assumed behavior of User we may conclude that
  (CA1) and (CA2) holds.


  We are now ready to prove the following properties for the composed system:

    sys_live1_lem =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (Arb U User)
        ==>
          req2 /\ gr1 LEADSTO req2 /\ gr1 /\ ~ req1 \/ gr2 IN (arb_prog U User)

    sys_live2_lem =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req2 /\ gr1 /\ ~ req1 LEADSTO gr2 IN (arb_prog U User)

    sys_live3_lem =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req2 /\ gr1 LEADSTO gr2 IN (arb_prog U User)

    sys_live4_lemma1 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req2 /\ gr2 /\ ~ gr1 LEADSTO gr2 IN (arb_prog U User)

    use_safe_lemma1 =
       !User.
       !i. reqi UNLESS gri IN User) ==> !i. ~gri STABLE IN User
          ==> !i. reqi /\ ~gri STABLE IN User)

    sys_live4_lemma2 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
        ==>
         req1 /\ ~gr1 /\ req2 /\ ~ gr2 LEADSTO gr1 /\ req2 IN (arb_prog U User)

    sys_live4_lemma3 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ ~gr1 /\ req2 /\ ~ gr2 LEADSTO gr2 IN (arb_prog U User)

    sys_live4_lemma4 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> ~req1 /\ ~gr1 /\ req2 /\ ~ gr2 LEADSTO gr2 IN (arb_prog U User)

    sys_live4_lemma5 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> ~gr1 /\ req2 /\ ~ gr2 LEADSTO gr2 IN (arb_prog U User)

    sys_live4_lemma6 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> ~gr1 /\ req2 LEADSTO gr2 IN (arb_prog U User)

    sys_live4_lem =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req2 LEADSTO gr2 IN (arb_prog U User)

    sys_live5_lem1 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ ~ gr2 LEADSTO gr1 IN (arb_prog U User)

    sys_live5_lem2_1 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ gr1 /\ gr2 LEADSTO gr1 IN (arb_prog U User)

    sys_live5_lem2_2_1 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ ~gr1 /\ ~req2 /\ gr2 LEADSTO gr1 IN (arb_prog U User)

    sys_live5_lem2_2_2 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ ~gr1 /\ gr2 LEADSTO gr1 IN (arb_prog U User)

    sys_live5_lem2 =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 /\ gr2 LEADSTO gr1 IN (arb_prog U User)

    sys_live5_thm =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> req1 LEADSTO gr1 IN (arb_prog U User)


  Finally, the shown proofs allow us to prove the original proof goal:

    sys_live_thm =
       !i User. (U1) /\ (U2) /\ (U3) /\ (U4) /\
       !i. gri LEADSTO ~reqi IN (arb_prog U User)
          ==> !i. reqi LEADSTO gri IN (arb_prog U User)


%
%*****************************************************************************%


system `/bin/rm example03.th`;;

set_flag(`timing`,true);;

loadt`l_unity`;;

new_theory`example03`;;

%
  INTRODUCTION.

%

%
  Some useful theorems, why can't I find them in HOL?
%
let NOT_AND_EQ_THM = TAC_PROOF
  (([],
   "(!P. P /\ ~P = F) /\  (!P. ~P /\ P = F)"),
   REWRITE_TAC [GEN_ALL NOT_AND;DE_MORGAN_THM;EXCLUDED_MIDDLE]);;

let CONJ_IMP_THM = TAC_PROOF
  (([],
   "!p1 p2 q. ((p1 /\ p2) ==> q) = (p1 ==> p2 ==> q)"),
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;


%
  Some tactics used in the proving
%

%
  [t1]...[tn] |- t   --->   |- t1 ==> ... ==> tn ==> t
%
let UNDISCH_ALL_TAC =
  let th_tac = (\(th:thm) (tac:tactic). (UNDISCH_TAC (concl th)) THEN tac) in
  let u_asml = (\thml:thm list. itlist  th_tac thml ALL_TAC)
in
   ASSUM_LIST u_asml;;

let UNDISCH_ONE_TAC =
  let th_tac = (\(th:thm) (tac:tactic). (UNDISCH_TAC (concl th)) THEN tac) in
  let u_asm  = (\th:thm. itlist  th_tac [th] ALL_TAC)
in
   FIRST_ASSUM u_asm;;


%
  Now we define a type representing two users, this is very easy using the
  type package made by Tom Melham.

  In general we would define a type corresponding to every variable in the
  composed programs.

	Var1, ..., Varn

  let var_Axiom = define_type `var_Axiom` `var = Var1 | ... | Varn`;;

  These could simply be used for representing the state mapping from these 
  names onto their values if they have equal types.

     The program variables could then be defined as:

	var1 = \s. s Var1

          ...

	varn = \s. s Varn

  However, if the variables have different types, the value domain may be 
  defined as the union of all variable types:

  let val_Axiom = define_type `val_Axiom` `val = TVal1 Tp1 | ... | TValn Tpn`;;

  To get the values of a type we define value selectors:

  let s_Val1  =  new_recursive_definition false val_Axiom `s_Val1`
       "!v:Tp1. s_Val1(TVal1 v) = v";;

     ...

  let s_Valn  =  new_recursive_definition false val_Axiom `s_Valn`
       "!v:Tpn. s_Valn(TValn v) = v";;

  These value selectors may now be used for defining state dependent variables
  together with the variable names, but first we introduce a shorthand for the
  state type:

  let STp = ":var->val";;

  let var1 = new_definition(`var1`, "var1 (s:^STp) = s_Val1(s Var1)");;

  ...

  let varn = new_definition(`varn`, "varn (s:^STp) = s_Valn(s Varn)");;


  The specification of this example however, introduces indexing on request
  req i, and grant gr i.

  Hence, we introduce another way of representing the state allowing for such
  indexing both in the specification and in the program.

  We define a type represing the use of either the first or the second branch
  of the arbiter:
%
let user_Axiom = define_type `user_Axiom` `user = U1 | U2`;;

%
  To prove some properties of this type we need an induction theorem for
  the user type:
%
let user_Induct = prove_induction_thm user_Axiom;;

%
  Make the induction theorem a tactic:
%
let user_INDUCT_TAC = INDUCT_THEN user_Induct ASSUME_TAC;;

%
  To prove the needed properties, we must have some additionally information
  about the type:

     -- such additionally theorems may now be part of the type definition --
     -- system, but unfortunately I don't know how and where              --
%
let exists_user_thm =
      prove_rec_fn_exists user_Axiom "(f U1 = T) /\ (f U2 = F)";;

%
  Now we are able to prove some trivial theorems about the type user, which
  are needed to prove the properties of the example:
%
let user_thm1 = TAC_PROOF
  (([],
   "~(U1 = U2) /\ ~(U2 = U1)"),
   REPEAT STRIP_TAC THEN
   MP_TAC exists_user_thm THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

%
  We are now ready to define the needed state varibles representing request for
  user i (req i), and grant from arbiter i (gr i).

  To do this we define a state as the mapping from U1 and U2 to their pair of
  boolean values. The first in the pair will represent the reguest and the
  second will be the grant value:
%
let STp = ":user->(bool#bool)";;

%
  This state may now be used for defining the needed indexed variables:
%
let req = new_definition (`req`,
   "req (i:user) = (\s:^STp. FST (s i))");;

let gr = new_definition (`gr`,
   "gr  (i:user) = (\s:^STp. SND (s i))");;

%
  Prove that req and gr are different.

  We need some lemmas for easing the proof:
%
let user_lemma1 = TAC_PROOF
  (([], "~(!s:^STp. FST(s U1) = SND(s U1))"),
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC "\u:user. (b1:bool,~b1:bool)" THEN
   BETA_TAC THEN
   REWRITE_TAC [FST;SND] THEN
   ASM_CASES_TAC "b1:bool" THEN % 2 Subgoals % ASM_REWRITE_TAC []);;

let user_lemma2 = TAC_PROOF
  (([], "((\s:^STp. FST(s U1)) = (\s. SND(s U1))) ==>
                (!s:^STp. (\s. FST(s U1))s = (\s. SND(s U1))s)"),
   DISCH_TAC THEN ASM_REWRITE_TAC []);;

let user_lemma3 = TAC_PROOF
  (([], "((\s:^STp. FST(s U1)) = (\s. SND(s U1))) ==>
                  (!s:^STp. FST(s U1) = SND(s U1))"),
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL user_lemma2) THEN
   UNDISCH_TAC "!s:^STp. (\s. FST(s U1))s = (\s. SND(s U1))s" THEN
   BETA_TAC THEN
   REWRITE_TAC []);;

let user_lemma4 = TAC_PROOF
  (([], "~(!x:user. req x = gr x)"),
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC "U1" THEN
   REWRITE_TAC [req;gr] THEN
   DISCH_TAC THEN
   MP_TAC user_lemma1 THEN
   REWRITE_TAC [] THEN
   GEN_TAC THEN
   ACCEPT_TAC (SPEC_ALL (UNDISCH_ALL user_lemma3)));;

%
  Finally we are ready to prove that the variables are different:
%
let user_thm2 = TAC_PROOF
  (([],
   "~(req = gr) /\ ~(gr = req)"),
   ASSUME_TAC user_lemma4 THEN
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC "~(!x. req x = gr x)" THEN
   ASM_REWRITE_TAC []);;


%
  The initial condition is defined as all variables having the value false:
%
let IC = "(~*(req U1) /\* ~*(req U2) /\* ~*(gr U1) /\* ~*(gr U2))";;

%
  A 2-Arbiter Program
  ===================

  We now give a definition of a program which will be proved to have the
  required compositional safety and progress properties.

%

%
  In HOL-UNITY, a program is represented as a list of state transitions in
  which new states may be conditionally chosen.

  To represent state transitions we introduce the shorthand:
%
let StrTp = ":^STp->^STp";;

%
  And the program type by:
%
let PrTp = ":(^StrTp)list";;

%
  Now we are ready to define the assignments with conditional values:
%


%
  We define the first assign statement

      gr U1 := TRUE    if (req U1 /\* ~*(gr U2)

  by the state transition which only change the state if the user is U1.
  Further the variable gr U1 is only changed if the condition is true in the
  given state. All other values are let unchanged in the new state.

  The following lambda expression defines the wanted state transition
  reflecting the perhaps more readable assignment given above:
%
let grantleft =
 "\s. \i. (i = U1) => (req U1 s, ((req U1 /\* ~*(gr U2))s => TRUE s | gr U1 s))
                   | s i";;

%
  Similarly the assignment

      gr U2 := TRUE    if (~*(req U1)) /\* (~*(gr U1)) /\* (req U2)

  is defined by:
%
let grantright =
 "\s. \i. (i = U2) => (req U2 s,
            (((~*(req U1)) /\* (~*(gr U1)) /\* (req U2))s => TRUE s | gr U2 s))
                   | s i";;


%
  In the assignment

       gr U1, gr U2 := FALSE, req U2   if (~*(req U1)) /\* (gr U1)

  two variables are changed.  Hence, we must define the assignment as the
  state transition changing both (gr U1) and (gr U2).  Notice that both
  values need a state satisfying the enabling condition before it may be
  changed.

  The following lambda expression defines the wanted transition and change
  of values in the state:
%
let doneleft   =
 "\s. \i. (i = U1) => (req U1 s, (((~*(req U1)) /\* (gr U1))s => FALSE s
                                                              | gr U1 s))
                   |
         ((i = U2) => (req U2 s, (((~*(req U1)) /\* (gr U1))s => (req U2)s
                                                               | gr U2 s))
                   | s i)";;

%
  The assignment

       gr U2 := FALSE   if (~*(req U2)) /\* (gr U2)

  is defined by:
%
let doneright  =
  "\s. \i. (i = U2) => (req U2 s, (((~*(req U2)) /\* (gr U2))s => FALSE s
                                                           | gr U2 s))
                    | s i";;

%
  These definitions enable us to define the wanted program:
%
let arb_prog =  "[^grantleft;^grantright;^doneleft;^doneright]";;

%
  The Specification.
  ==================

  The method used here is an attempt to bind properties to a certain component.
  This way of specifying may be changed if a better idea turns up.
%

%
  Unconditional properties given for the Arbiter component:
                                         ==================
%
let arb_safe1 = new_definition (`arb_safe1`,
  "arb_safe1 Arb IC = (~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb)");;

let arb_safe2 = new_definition (`arb_safe2`,
  "arb_safe2 Arb (IC:^STp->bool) = !i:user. (req i) STABLE Arb");;

let arb_safe3 = new_definition (`arb_safe3`,
  "arb_safe3 Arb (IC:^STp->bool) = !i:user. (~*(req i)) STABLE Arb");;

let arb_safe4 = new_definition (`arb_safe4`,
  "arb_safe4 Arb (IC:^STp->bool) = !i:user. ((gr i) UNLESS (~*(req i))) Arb");;

%
  Unconditional properties given for the User component:
                                         ===============
%
let use_safe1 = new_definition (`use_safe1`,
  "use_safe1 User (IC:^STp->bool) = !i:user. (gr i) STABLE User");;

let use_safe2 = new_definition (`use_safe2`,
  "use_safe2 User (IC:^STp->bool) = !i:user. (~*(gr i)) STABLE User");;

let use_safe3 = new_definition (`use_safe3`,
  "use_safe3 User (IC:^STp->bool) = !i:user. ((req i) UNLESS (gr i)) User");;

let use_safe4 = new_definition (`use_safe4`,
  "use_safe4 User (IC:^STp->bool) =
      !i:user. ((~*(req i)) UNLESS (~*(gr i))) User");;

%
  Conditional properties given for the Arbiter component:
                                       ==================
%
let c_arb_live1 = new_definition (`c_arb_live1`,
   "c_arb_live1 Arb (IC:^STp->bool) =
     !(i:user) (User:^PrTp).
          use_safe1 User IC /\ use_safe2 User IC /\
          use_safe3 User IC /\ use_safe4 User IC /\
          ((gr i)  LEADSTO (~*(req i))) (APPEND Arb User) ==>
          ((req i) LEADSTO (gr i)) (APPEND Arb User)");;

let c_arb_live2 = new_definition (`c_arb_live2`,
   "c_arb_live2 Arb (IC:^STp->bool) =
     !(i:user) (User:^PrTp).
          use_safe1 User IC /\ use_safe2 User IC /\
          use_safe3 User IC /\ use_safe4 User IC /\
          ((gr i)  LEADSTO (~*(req i))) (APPEND Arb User) ==>
          (((gr i) /\* (~*(req i))) LEADSTO (~*(gr i))) (APPEND Arb User)");;

%
  Conditional properties given for the User component:
                                       ===============
%
let c_use_live1 = new_definition (`c_use_live1`,
   "c_use_live1 User (IC:^STp->bool) =
     !(i:user) (Arb:^PrTp).
       arb_safe2 Arb IC /\ arb_safe3 Arb IC /\ arb_safe4 Arb IC /\
       ((~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User))) ==>
             ((gr i) LEADSTO (~*(req i))) (APPEND Arb User)");;

%
  Complete properties given for the User component:
                                    ===============
%
let use_spec =
   "\User IC. use_safe1 User (IC:^STp->bool) /\ use_safe2 User IC /\
              use_safe3 User IC /\ use_safe4 User IC /\ c_use_live1 User IC";;

%
  Complete properties given for the Arbiter component:
                                    ==================
%
let arb_spec =
   "\Arb IC. arb_safe1 Arb (IC:^STp->bool) /\ arb_safe2 Arb IC /\
              arb_safe3 Arb IC /\
              arb_safe4 Arb IC /\ c_arb_live1 Arb IC /\ c_arb_live2 Arb IC";;

%------------------------------------------------------------------------------
*									      *
*			Derived properties				      *
*									      *
------------------------------------------------------------------------------%


%
   Prove that the composed system satisfies:
%
let mutex_thm0 = TAC_PROOF
  (([],
   "!User Arb IC. use_safe2 User IC /\ arb_safe1 Arb IC
        ==> (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User))"),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [use_safe2;arb_safe1] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC
        "U1:user" (ASSUME "!i:user. (~*(gr i)) STABLE User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC
        "U2:user" (ASSUME "!i:user. (~*(gr i)) STABLE User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["(~*(gr (U1:user))) STABLE User";"(~*(gr (U2:user))) STABLE User"]
         AND_INTRO_THM)) THEN
   UNDISCH_TAC
        "(~*(gr (U1:user))) STABLE User /\ (~*(gr U2)) STABLE User" THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["~*(gr (U1:user))";"FALSE:^STp->bool";
         "~*(gr (U2:user))";"FALSE:^STp->bool";
         "User:^PrTp"]
         UNLESS_thm7)) THEN
   UNDISCH_TAC
     "(((~*(gr (U1:user))) \/* (~*(gr U2))) UNLESS (FALSE \/* FALSE))User" THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL NOT_AND_OR_NOT_lemma))] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL STABLE))] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["(~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb)";
         "(~*((gr U1) /\* (gr U2))) STABLE User"] AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["IC:^STp->bool";"~*((gr (U1:user)) /\* (gr U2))";
         "Arb:^PrTp";
         "User:^PrTp"]
         COMP_UNITY_cor3)));;

%
   Prove that the composed system satisfies:

%
let mutex_thm1 = TAC_PROOF
  (([],
   "!(i:user) User Arb IC. ^use_spec User IC /\ ^arb_spec Arb IC
        ==> ((req i) LEADSTO (gr i)) (APPEND Arb User)"),
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL mutex_thm0) THEN
   UNDISCH_TAC (snd (dest_thm (SPEC_ALL mutex_thm0))) THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4;c_use_live1;
                arb_safe1;arb_safe2;arb_safe3;arb_safe4;c_arb_live1] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["!i:user. (~*(gr i)) STABLE User";
         "~*((gr U1) /\* (gr U2)) INVARIANT (IC, Arb)"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ASSUME
        "(!i:user. (~*(gr i)) STABLE User) /\
         (~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb) ==>
           (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User))")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!(i:user) Arb.
        (!i. (req i) STABLE Arb) /\
        (!i. (~*(req i)) STABLE Arb) /\
        (!i. ((gr i) UNLESS (~*(req i)))Arb) /\
        (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User)) ==>
        ((gr i) LEADSTO (~*(req i)))(APPEND Arb User)")) THEN
   RES_TAC);;

%
   Prove that the composed system satisfies:
%
let mutex_thm2 = TAC_PROOF
  (([],
   "!(i:user) User Arb IC. ^use_spec User IC /\ ^arb_spec Arb IC
        ==> ((gr i) LEADSTO (~*(req i))) (APPEND Arb User)"),
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL mutex_thm0) THEN
   UNDISCH_TAC (snd (dest_thm (SPEC_ALL mutex_thm0))) THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4;c_use_live1;
                arb_safe1;arb_safe2;arb_safe3;arb_safe4;c_arb_live1] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["!i:user. (~*(gr i)) STABLE User";
         "(~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb)"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ASSUME
        "(!i:user. (~*(gr i)) STABLE User) /\
         (~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb) ==>
           (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User))")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!(i:user) Arb.
        (!i. (req i) STABLE Arb) /\
        (!i. (~*(req i)) STABLE Arb) /\
        (!i. ((gr i) UNLESS (~*(req i)))Arb) /\
        (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User)) ==>
        ((gr i) LEADSTO (~*(req i)))(APPEND Arb User)")) THEN
   RES_TAC);;

%
   Prove that the composed system satisfies:
%
let mutex_thm3 = TAC_PROOF
  (([],
   "!(i:user) User Arb IC. ^use_spec User IC /\ ^arb_spec Arb IC
         ==> ((req i) LEADSTO (~*(req i))) (APPEND Arb User)"),
   BETA_TAC THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (BETA_RULE mutex_thm1))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (BETA_RULE mutex_thm2))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["((req (i:user)) LEADSTO (gr i))(APPEND Arb User)";
         "((gr (i:user)) LEADSTO (~*(req i)))(APPEND Arb User)"]
         AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["req (i:user)";"gr (i:user)";"~*(req (i:user))";
         "APPEND (Arb:^PrTp) User"]
         LEADSTO_thm1)));;

%
   Prove that the composed system satisfies:

%
let mutex_thm4 = TAC_PROOF
  (([],
   "!(i:user) User Arb IC. ^use_spec User IC /\ ^arb_spec Arb IC
       ==> (((gr i) /\* (~*(req i))) LEADSTO (~*(gr i))) (APPEND Arb User)"),
   BETA_TAC THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC_ALL mutex_thm0) THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4;c_use_live1;
                arb_safe1;arb_safe2;arb_safe3;arb_safe4;c_arb_live2] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
        ["!i:user. (~*(gr i)) STABLE User";
         "(~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb)"]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ASSUME
        "(!i:user. (~*(gr i)) STABLE User) /\
         (~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb) ==>
           (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User))")) THEN
   ASSUME_TAC (SPEC_ALL (ASSUME "!(i:user) Arb.
        (!i. (req i) STABLE Arb) /\
        (!i. (~*(req i)) STABLE Arb) /\
        (!i. ((gr i) UNLESS (~*(req i)))Arb) /\
        (~*((gr U1) /\* (gr U2))) INVARIANT (IC, (APPEND Arb User)) ==>
        ((gr i) LEADSTO (~*(req i)))(APPEND Arb User)")) THEN
   RES_TAC);;


%
  Proof of arbiter program properties
%

%
  We define a tactic which is able to prove the claimed safety properties
  (UNLESS, STABLE, INVARIANT) and the basic progress properties
  (EXIST_TRANSITION) properties of the program:
%
let PROVE_PROG_TAC =
   REWRITE_TAC
    [UNLESS;UNLESS_STMT;EXIST_TRANSITION;ENSURES;STABLE;INVARIANT;
     ~*;/\*;\/*;TRUE_DEF;FALSE_DEF;req;gr;user_thm1;user_thm2] THEN
   BETA_TAC THEN
   REWRITE_TAC
     [NOT_CLAUSES;AND_CLAUSES;OR_CLAUSES;DE_MORGAN_THM;EXCLUDED_MIDDLE] THEN
   REPEAT STRIP_TAC THEN
   (ASM_REWRITE_TAC [] THEN
    BETA_TAC THEN ASM_REWRITE_TAC [user_thm1] THEN RES_TAC THEN
    UNDISCH_ONE_TAC THEN
    ASM_REWRITE_TAC [] THEN
    BETA_TAC THEN ASM_REWRITE_TAC [user_thm1] THEN RES_TAC) THEN
   STRIP_TAC THEN
   REPEAT COND_CASES_TAC THEN BETA_TAC THEN REWRITE_TAC [] THEN BETA_TAC THEN
   ASM_REWRITE_TAC [user_thm1;user_thm2;EXCLUDED_MIDDLE] THEN
   UNDISCH_ONE_TAC THEN REPEAT COND_CASES_TAC THEN BETA_TAC THEN
   ASM_REWRITE_TAC [user_thm1;user_thm2;EXCLUDED_MIDDLE];;


%
  First we prove, that all the given safety properties for the arbiter is
  satisfied by the given program:
%

%
  arb_safe1 Arb IC = (~*((gr U1) /\* (gr U2))) INVARIANT (IC, Arb)
%

%
  First we prove that the given initial condition implies mutual exclusion:

	!s. IC s ==> ~*((gr U1) /\* (gr U2)) s
%

let init_lemma = TAC_PROOF
  (([],
   "(IC = ^IC) ==> (!s:^STp. IC s ==> ~*((gr U1) /\* (gr U2)) s)"),
   DISCH_TAC THEN
   ASM_REWRITE_TAC [] THEN
   PROVE_PROG_TAC);;


%
  We have proved "init_lemma" that initially
        ~*((gr U1) /\* (gr U2)) 
  using the lemma "init_lemma", we may prove that the invariant
	~*((gr U1) /\* (gr U2)) INVARIANT (IC, Arb)
  holds for the entire program
%
let arb_safe1_thm = TAC_PROOF
  (([],
   "(IC = ^IC) ==> (~*((gr U1) /\* (gr U2))) INVARIANT (IC, ^arb_prog)"),
   DISCH_TAC THEN
   REWRITE_TAC [INVARIANT;UNDISCH init_lemma] THEN
   PROVE_PROG_TAC);;

%
   Now we want to prove, that the second safety property of the arbiter
   specification is satisfied by the given program.

	arb_safe2 Arb IC = !i:user. (req i) STABLE Arb
%
let arb_safe2_thm = TAC_PROOF
  (([],
   "!i:user. (req i) STABLE ^arb_prog"),
   user_INDUCT_TAC THEN PROVE_PROG_TAC);;

%
   We proceed in just the same way as before for the third safety property

	arb_safe3 Arb IC = !i. (~*(req i)) STABLE Arb
%
let arb_safe3_thm = TAC_PROOF
  (([],
   "!i:user. (~*(req i)) STABLE ^arb_prog"),
   user_INDUCT_TAC THEN PROVE_PROG_TAC);;

%
   Finally for the fourth safety property:
	arb_safe4 Arb IC = !i. ((gr i) UNLESS (~*(req i))) Arb
%
let arb_safe4_thm = TAC_PROOF
  (([],
   "!i:user. ((gr i) UNLESS (~*(req i))) ^arb_prog"),
   user_INDUCT_TAC THEN PROVE_PROG_TAC);;

%
  Now we are ready to show how one may prove progress (LEADSTO) properties
  from basic properties (ENSURES) satisfied by the arbiter program.
%

%
  First the needed unless properties for the chosen ensures.
%
let arb_safe_tr1_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) UNLESS
     ((gr U1) /\* (req U1) /\* (~*(gr U2)))) ^arb_prog"),
   PROVE_PROG_TAC);;

let arb_safe_tr2_thm = TAC_PROOF
  (([],
   "(((req U2) /\* (~*(req U1)) /\* (~*(gr U1))) UNLESS
     ((gr U2) /\* (req U2) /\* (~*(req U1)) /\* (~*(gr U1)))) ^arb_prog"),
   PROVE_PROG_TAC);;

let arb_safe_tr3_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\*  (gr U1)) UNLESS
     ((~*( gr U1)) /\*
     (((gr U2) /\* (req U2)) \/* ((~*(gr U2)) /\* (~*(req U2)))) /\*
     (~*(req U1))))
     ^arb_prog"),
   PROVE_PROG_TAC);;

let arb_safe_tr4_thm = TAC_PROOF
  (([],
   "(((~*(req U2)) /\* (gr U2)) UNLESS ((~*(gr U2)) /\* (~*(req U2))))
      ^arb_prog"),
   PROVE_PROG_TAC);;

%
   Now we are ready to the proving of ensures properties
%

%
   For each program transition we now prove, that the wanted ensures property
   of the transition is satisfied. These ensures properties make use of the 
   previously proved unless safety properties. Hence we only need to prove the
   existance of the respective transitions for the ensures properties.
%
let arb_trans_tr1_lem = TAC_PROOF
  (([], "(((req U1) /\* (~*(gr U2))) EXIST_TRANSITION
          ((gr U1) /\* (req U1) /\* (~*(gr U2)))) [^grantleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr1_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) EXIST_TRANSITION
     ((gr U1) /\* (req U1) /\* (~*(gr U2)))) ^arb_prog"),
   MP_TAC arb_trans_tr1_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr1_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) ENSURES
     ((gr U1) /\* (req U1) /\* (~*(gr U2)))) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr1_thm;arb_trans_tr1_thm]);;

let arb_trans_tr2_lem = TAC_PROOF
  (([],
   "(((req U2) /\* (~*(req U1)) /\* (~*(gr U1))) EXIST_TRANSITION
          ((gr U2) /\* (req U2) /\* (~*(req U1)) /\* (~*(gr U1))))
       [^grantright]"),
   PROVE_PROG_TAC);;

let arb_trans_tr2_thm = TAC_PROOF
  (([],
   "(((req U2) /\* ((~*(req U1)) /\* (~*(gr U1)))) EXIST_TRANSITION
     ((gr U2) /\* (req U2) /\* (~*(req U1)) /\* (~*(gr U1)))) ^arb_prog"),
   MP_TAC arb_trans_tr2_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr2_thm = TAC_PROOF
  (([],
   "(((req U2) /\* ((~*(req U1)) /\* (~*(gr U1)))) ENSURES
     ((gr U2) /\* (req U2) /\* (~*(req U1)) /\* (~*(gr U1)))) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr2_thm;arb_trans_tr2_thm]);;

let arb_trans_tr3_lem = TAC_PROOF
  (([],
   "(((~*(req U1)) /\*  (gr U1)) EXIST_TRANSITION
         ((~*( gr U1)) /\*
         (((gr U2) /\* (req U2)) \/* ((~*(gr U2)) /\* (~*(req U2)))) /\*
         (~*(req U1))))
      [^doneleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr3_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\*  (gr U1)) EXIST_TRANSITION
     ((~*( gr U1)) /\*
     (((gr U2) /\* (req U2)) \/* ((~*(gr U2)) /\* (~*(req U2)))) /\*
       (~*(req U1))))
      ^arb_prog"),
   MP_TAC arb_trans_tr3_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr3_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\*  (gr U1)) ENSURES
     ((~*( gr U1)) /\*
     (((gr U2) /\* (req U2)) \/* ((~*(gr U2)) /\* (~*(req U2)))) /\*
       (~*(req U1))))
      ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr3_thm;arb_trans_tr3_thm]);;

let arb_trans_tr4_lem = TAC_PROOF
  (([],
   "(((~*(req U2)) /\* (gr U2)) EXIST_TRANSITION 
          ((~*(gr U2)) /\* (~*(req U2)))) [^doneright]"),
   PROVE_PROG_TAC);;

let arb_trans_tr4_thm = TAC_PROOF
  (([],
   "(((~*(req U2)) /\* (gr U2)) EXIST_TRANSITION
     ((~*(gr U2)) /\* (~*(req U2)))) ^arb_prog"),
   MP_TAC arb_trans_tr4_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr4_thm = TAC_PROOF
  (([],
   "(((~*(req U2)) /\* (gr U2)) ENSURES ((~*(gr U2)) /\* (~*(req U2))))
      ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr4_thm;arb_trans_tr4_thm]);;


%
  Having proven some progress properties of the arbiter program we would
  like to prove that the conditional progress (LEADSTO) property is satisfied
  by the safety properties of the program
%

%
  First we prove:

	req2 /\ gr1 --> req2 /\ gr1 /\ ~req1 \/ gr2 in S

  assuming the safety properties given from the specifications, and the
  additional conditional progress (LEADSTO) property for the composed system.
%
let sys_live1_lem_1 = TAC_PROOF
  (([],
   "!st (arb_prog:^PrTp) arb_prog'.
       ((CONS st arb_prog') = arb_prog) ==>
            ((CONS st(APPEND arb_prog' User) = (APPEND arb_prog User)))"),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [SYM (ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)")] THEN
   REWRITE_TAC [APPEND]);;

let sys_live1_lem = TAC_PROOF
  (([],
   "!User.
    (IC = ^IC) /\ ((CONS st arb_prog') = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
          (((req U2) /\* (gr U1)) LEADSTO
          (((req U2) /\* (gr U1) /\* (~* (req U1))) \/* (gr U2)))
          (APPEND arb_prog User)"),
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC "U1" arb_safe2_thm) THEN
   ASSUME_TAC (SPEC "U1" arb_safe4_thm) THEN
   UNDISCH_ONE_TAC THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U1) UNLESS (~*(req U1)))arb_prog";
      "(req U1) STABLE arb_prog"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["gr U1";"req U1";
      "arb_prog:^PrTp"]
      UNLESS_cor14)) THEN
   ASSUME_TAC (SPEC "U1" (ASSUME "!i:user. (gr i) STABLE User")) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U1) UNLESS ((gr U1) /\* (~*(req U1))))arb_prog";
      "(gr U1) STABLE User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["gr U1";"(gr U1) /\* (~*(req U1))";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      COMP_UNITY_cor2)) THEN
   ASSUME_TAC (SPEC "U1" (ASSUME
     "!i:user. ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)")) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U1) LEADSTO (~*(req U1)))(APPEND arb_prog User)";
      "((gr U1) UNLESS ((gr U1) /\* (~*(req U1))))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)]
    (ISPECL
      ["gr U1";"~*(req U1)";"gr U1";"(gr U1) /\* (~*(req U1))";
       "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
       LEADSTO_thm29))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [AND_AND_lemma] THEN
   ONCE_REWRITE_TAC [OR_AND_COMM_lemma] THEN
   REWRITE_TAC [OR_OR_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC "U2" (ASSUME "!i. ((req i) UNLESS (gr i))User")) THEN
   UNDISCH_ONE_TAC THEN
   ASSUME_TAC (SPEC "U2" arb_safe2_thm) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U2) STABLE arb_prog";"((req U2) UNLESS (gr U2))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["req U2";"gr U2";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      COMP_UNITY_cor9)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U1) LEADSTO ((~*(req U1)) /\* (gr U1)))(APPEND arb_prog User)";
      "((req U2) UNLESS (gr U2))(APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)]
    (ISPECL
     ["gr U1";"(~*(req U1)) /\* (gr U1)";"req U2";"gr U2";
       "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
      LEADSTO_thm29))) THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_AND_lemma] THEN
   ASM_REWRITE_TAC []);;

%
  Next we prove:
	req2 /\ gr1 /\ ~reg1 --> gr2 in S
%

%
   To prove this we need to prove, that the ensures property of the given
   leadsto property holds for the program. This like before is a two step
   proof:
      1) Prove that the unless holds
      2) Prove that a transition validates the property.
   From this the ensures property can be proven.
%

%
  First the safety property.

  Just as before we prove that the unless holds for every transition and then
  that it holds for the entire program.
%
let arb_safe_tr2a_thm = TAC_PROOF
  (([],
   "(((req U2) /\* (~*(req U1)) /\* (gr U1)) UNLESS (gr U2)) ^arb_prog"),
   PROVE_PROG_TAC);;

%
  Then the basic progress property.
%
let arb_trans_tr2a_lem = TAC_PROOF
  (([],
   "(((req U2) /\* (~*(req U1)) /\* (gr U1)) EXIST_TRANSITION (gr U2))
       [^doneleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr2a_thm = TAC_PROOF
  (([],
   "(((req U2) /\* ((~*(req U1)) /\* (gr U1))) EXIST_TRANSITION (gr U2))
      ^arb_prog"),
   MP_TAC arb_trans_tr2a_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr2a_thm = TAC_PROOF
  (([],
   "(((req U2) /\* ((~*(req U1)) /\* (gr U1))) ENSURES (gr U2)) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr2a_thm;arb_trans_tr2a_thm]);;

%
  Finally the proof:

	req2 /\ gr1 /\ ~reg1 --> gr2 in S
%
let sys_live2_lem = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
          (((req U2) /\* ((gr U1) /\* (~* (req U1)))) LEADSTO (gr U2))
          (APPEND arb_prog User)"),
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC arb_live_tr2a_thm THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC "U1" (ASSUME "!i. (gr i) STABLE User")) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC "U1" (ASSUME
      "!i. ((~*(req i)) UNLESS (~*(gr i)))User")) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U1) UNLESS FALSE)User";"((~*(req U1)) UNLESS (~*(gr U1)))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["gr U1";"FALSE:^STp->bool";"~*(req U1)";"~*(gr U1)";
      "User:^PrTp"]
      UNLESS_thm4)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [P_AND_NOT_P_lemma;AND_FALSE_lemma;OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC "U2" (ASSUME "!i. ((req i) UNLESS (gr i))User")) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((req U2) UNLESS (gr U2))User";
      "(((gr U1) /\* (~*(req U1))) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["req U2";"gr U2";"(gr U1) /\* (~* (req U1))";"FALSE:^STp->bool";
      "User:^PrTp"]
      UNLESS_thm6)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   DISCH_TAC THEN
   UNDISCH_TAC "(((req U2) /\* ((~*(req U1)) /\* (gr U1))) ENSURES (gr U2))
                arb_prog" THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   DISCH_TAC THEN
   UNDISCH_TAC
      "(((req U2) /\* ((~*(req U1)) /\* (gr U1))) UNLESS (gr U2))User" THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U2) /\* ((gr U1) /\* (~*(req U1)))) ENSURES (gr U2))arb_prog";
      "(((req U2) /\* ((gr U1) /\* (~*(req U1)))) UNLESS (gr U2))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U2) /\* ((gr U1) /\* (~*(req U1)))) ENSURES (gr U2))arb_prog /\
       (((req U2) /\* ((gr U1) /\* (~*(req U1)))) UNLESS (gr U2))User";
      "(((req U2) /\* ((gr U1) /\* (~*(req U1)))) ENSURES (gr U2))User /\
       (((req U2) /\* ((gr U1) /\* (~*(req U1)))) UNLESS (gr U2))arb_prog"]
      OR_INTRO_THM1)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U2) /\* ((gr U1) /\* (~*(req U1)))";"gr U2";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL COMP_ENSURES_thm1)))))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U2) /\* ((gr U1) /\* (~*(req U1)))";"gr U2";
      "APPEND arb_prog (User:^PrTp)"]
      LEADSTO_thm0)) THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

%
   Applying the proofs 

	req2 /\ gr1 --> req2 /\ gr1 /\ ~req1 \/ gr2 in S,
	req2 /\ gr1 /\ ~reg1 --> gr2 in S

   to the theorem:

	p --> q \/ b, b --> r
        ---------------------
	    p --> q \/ r

   we are able to deduce the result:

	req2 /\ gr1 --> gr2 in S
%
let sys_live3_lem = TAC_PROOF
  (([],
   "!User.
    (IC = ^IC) /\ ((CONS st arb_prog') = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
          (((req U2) /\* (gr U1)) LEADSTO (gr U2))(APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live1_lem))) THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live2_lem))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U2) /\* (gr U1)) LEADSTO
        ((gr U2) \/* ((req U2) /\* ((gr U1) /\* (~*(req U1))))))
       (APPEND arb_prog User)";
      "(((req U2) /\* ((gr U1) /\* (~*(req U1)))) LEADSTO (gr U2))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)]
    (ISPECL
     ["(req U2) /\* (gr U1)";"gr U2";
      "(req U2) /\* ((gr U1) /\* (~*(req U1)))";"gr U2";
      "st:^STp->^STp";"APPEND arb_prog' (User:^PrTp)"]
      LEADSTO_thm28))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_OR_lemma]);;

%
  This result was the first step in proving what we are really hunting for
  namely:
		reg2 --> gr2

  To prove this, we may use the theorem:

		p /\ q --> r, p /\ ~q --> r
		---------------------------
			p --> r

  this requires that we prove:

	1)	req2 /\ ~gr1 --> gr2 in S

  To prove this we need a proof of:

	1.1)	req2 /\ ~gr1 /\ gr2 --> gr2 in S, trivially by weakening
	1.2)	req2 /\ ~gr1 /\ ~gr2 --> gr2 in S

	   To prove this we need proofs of:
		1.2.1)	 req1 /\ req2 /\ ~gr1 /\ ~gr2 --> gr2 in S
		1.2.2)	~req1 /\ req2 /\ ~gr1 /\ ~gr2 --> gr2 in S

  This will finally lead us to the wanted proof by disjunction of all
  the subproofs.
%

%
  Prove:
	req2 /\ ~gr1 /\ gr2 --> gr2 in S
%
let sys_live4_lemma1 = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U2) /\* ((gr U2) /\* (~* (gr U1)))) LEADSTO (gr U2))
          (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [APPEND] THEN
   ACCEPT_TAC (MP
     (ISPECL ["(req U2) /\* ((gr U2) /\* (~*(gr U1)))";"gr U2";
             "^grantleft";
             "APPEND [^grantright;^doneleft;^doneright] User"]
             LEADSTO_thm25)
     (REWRITE_RULE [AND_ASSOC_lemma] (ONCE_REWRITE_RULE [AND_COMM_AND_lemma]
        (REWRITE_RULE [SYM (SPEC_ALL AND_ASSOC_lemma)] 
        (ISPECL ["gr U2";"(req U2) /\* ~*(gr U1)"]
                SYM_AND_IMPLY_WEAK_lemma))))));;


%
  Next we prove:
	req1 /\ ~gr1 /\ req2 /\ ~gr2 --> gr2 in S
%

%
   To prove this we need to prove, that the needed ensures properties of the
   given leadsto property holds for the program. This like before is a two step
   proof:
      1) Prove that the unless holds
      2) Prove that a transition validates the property.
   From this the ensures property can be proven.
%

%
  First the safety property.

  Just as before we prove that the unless holds for the program.
%
let arb_safe_tr1a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) UNLESS
      ((gr U1) /\* (req U2))) ^arb_prog"),
   PROVE_PROG_TAC);;

%
  Then the basic progress property.
%
let arb_trans_tr1a_lem = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
            EXIST_TRANSITION ((gr U1) /\* (req U2))) [^grantleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr1a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
            EXIST_TRANSITION ((gr U1) /\* (req U2))) ^arb_prog"),
   MP_TAC arb_trans_tr1a_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr1a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) ENSURES
     ((gr U1) /\* (req U2))) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr1a_thm;arb_trans_tr1a_thm]);;

%
  A useful lemma:
      !i User. reqi unless gri ==> ~gri stable ==> regi /\ ~gri stable
%
let use_safe_lemma1 = TAC_PROOF
  (([],
   "!User. (!i:user. ((req i) UNLESS (gr i))User) ==>
                (!i:user. (~*(gr i)) STABLE User) ==>
                   (!i:user. ((req i) /\* (~*(gr i))) STABLE User)"),
   REWRITE_TAC [STABLE] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "i:user" (ASSUME
     "!i. ((req i) UNLESS (gr i))User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "i:user" (ASSUME
     "!i. ((~*(gr i)) UNLESS FALSE)User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((req (i:user)) UNLESS (gr i))User";
      "((~*(gr (i:user))) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["req (i:user)";"gr (i:user)";"~* (gr (i:user))";"FALSE:^STp->bool";
      "User:^PrTp"]
      UNLESS_thm4)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma]);;

%
  Now the proof:
	req1 /\ ~gr1 /\ reg2 /\ ~gr2 --> gr2 in S
%
let sys_live4_lemma2 = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~* (gr U2))))) LEADSTO
          ((gr U1) /\* (req U2))) (APPEND arb_prog User)"),
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL use_safe_lemma1)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U1" (ASSUME
     "!i. (((req i) /\* (~*(gr i))) UNLESS FALSE)User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
     "!i. (((req i) /\* (~*(gr i))) UNLESS FALSE)User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* (~*(gr U1))) UNLESS FALSE)User";
      "(((req U2) /\* (~*(gr U2))) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* (~*(gr U1))";"FALSE:^STp->bool";
      "(req U2) /\* (~*(gr U2))";"FALSE:^STp->bool";
      "User:^PrTp"]
      UNLESS_thm4)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma] THEN
   REWRITE_TAC [AND_ASSOC_lemma;(GEN_ALL (SYM (SPEC_ALL STABLE)))] THEN
   DISCH_TAC THEN
   ASSUME_TAC arb_live_tr1a_thm THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) ENSURES
        ((gr U1) /\* (req U2)))
       arb_prog";
      "((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) STABLE
       User"]
   AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "(gr U1) /\* (req U2)";
      "arb_prog:^PrTp";
      "User:^PrTp"] 
      COMP_UNITY_cor4)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "(gr U1) /\* (req U2)";
      "APPEND arb_prog User:^PrTp"] 
      LEADSTO_thm0)));;

let sys_live4_lemma3 = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~* (gr U2))))) LEADSTO
          (gr U2)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live3_lem))) THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live4_lemma2))) THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))) /\* (req U1)) LEADSTO
        ((req U2) /\* (gr U1))) (APPEND arb_prog User)";
      "(((req U2) /\* (gr U1)) LEADSTO (gr U2))(APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))) /\* (req U1)";
      "(req U2) /\* (gr U1)";"gr U2";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_thm1)));;

%
  Yet another ensures property

  The safety property.
%
let arb_safe_tr2b_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
          UNLESS (gr U2)) ^arb_prog"),
   PROVE_PROG_TAC);;

%
  The basic progress property.
%
let arb_trans_tr2b_lem = TAC_PROOF
  (([],
   "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
          EXIST_TRANSITION (gr U2)) [^grantright]"),
   PROVE_PROG_TAC);;

let arb_trans_tr2b_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
          EXIST_TRANSITION (gr U2)) ^arb_prog"),
   MP_TAC arb_trans_tr2b_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr2b_thm = TAC_PROOF
  (([],
   "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
          ENSURES (gr U2)) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr2b_thm;arb_trans_tr2b_thm]);;

%
  The progress (LEADSTO) property:

	~req1 /\ ~gr1 /\ req2 /\ ~gr2 --> gr2
%
let sys_weak_lemma1 = TAC_PROOF
  (([],
   "!s. ((((((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) /\* (gr U2)) \/*
             ((~*(gr U2)) /\*
             (((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
             ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
             (((req U1) /\* (~*(gr U1))) /\* (gr U2))))) \/*
             ((((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
             ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
             (((req U1) /\* (~*(gr U1))) /\* (gr U2))) /\*
             (gr U2)))s ==>
             ((gr U2) \/*
             ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))))s"),
   REWRITE_TAC [/\*;\/*;~*;FALSE_DEF;TRUE_DEF] THEN
   BETA_TAC THEN
   REWRITE_TAC [AND_CLAUSES;OR_CLAUSES;NOT_CLAUSES;DE_MORGAN_THM] THEN
   REPEAT STRIP_TAC THEN % 7 Subgoals %
   ASM_REWRITE_TAC []);;

let sys_live4_lemma4 = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~* (gr U2)))))
        LEADSTO (gr U2)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live4_lemma3))) THEN
   UNDISCH_ALL_TAC THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC arb_live_tr2b_thm THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   ASSUME_TAC (ISPECL
     ["~*(req U1)";"User:^PrTp"]
      UNLESS_thm2) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U1" (ASSUME
     "!i. (~*(gr i)) STABLE User"))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((~*(req U1)) UNLESS (req U1))User";"((~*(gr U1)) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["~*(req U1)";"req U1";"~*(gr U1)";"FALSE:^STp->bool";
      "User:^PrTp"]
      UNLESS_thm4)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma] THEN
   ONCE_REWRITE_TAC [OR_AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_FALSE_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
     "!i. ((req i) UNLESS (gr i))User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\* (~*(gr U1))) UNLESS
       ((req U1) /\* (~*(gr U1))))User";
      "((req U2) UNLESS (gr U2))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(req U1)) /\* (~*(gr U1))";"(req U1) /\* (~*(gr U1))";"req U2";
      "gr U2";"User:^PrTp"]
      UNLESS_thm4)) THEN
   ASSUME_TAC (ISPECL
     ["~*(gr U2)";"User:^PrTp"]
      UNLESS_thm2) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) UNLESS
        (((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
          ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
         (((req U1) /\* (~*(gr U1))) /\* (gr U2))))User";
      "((~*(gr U2)) UNLESS (gr U2))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)";
      "((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
          ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
         (((req U1) /\* (~*(gr U1))) /\* (gr U2))";
      "~*(gr U2)";"gr U2";
      "User:^PrTp"]
      UNLESS_thm4)) THEN
   ASSUME_TAC sys_weak_lemma1 THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) /\*
         (~*(gr U2))) UNLESS
        ((((((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) /\* (gr U2)) \/*
          ((~*(gr U2)) /\*
           (((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
             ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
            (((req U1) /\* (~*(gr U1))) /\* (gr U2))))) \/*
         ((((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
            ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
           (((req U1) /\* (~*(gr U1))) /\* (gr U2))) /\*
          (gr U2))))
       User";
       (concl sys_weak_lemma1)]
       AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) /\* (~*(gr U2))";
      "(((((~*(req U1)) /\* (~*(gr U1))) /\* (req U2)) /\* (gr U2)) \/*
          ((~*(gr U2)) /\*
           (((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
             ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
            (((req U1) /\* (~*(gr U1))) /\* (gr U2))))) \/*
         ((((((~*(req U1)) /\* (~*(gr U1))) /\* (gr U2)) \/*
            ((req U2) /\* ((req U1) /\* (~*(gr U1))))) \/*
           (((req U1) /\* (~*(gr U1))) /\* (gr U2))) /\*
          (gr U2))";
      "(gr U2) \/*
       ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))";
      "User:^PrTp"]
      UNLESS_thm3)) THEN
   UNDISCH_ONE_TAC THEN
   ASSUME_TAC (ISPECL
     ["gr U2";"(req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))"]
      OR_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        ENSURES (gr U2)) arb_prog";
      "!s. gr U2 s ==> ((gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))))s"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "gr U2";
      "(gr U2) \/*
       ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))";
      "arb_prog:^PrTp"]
      ENSURES_thm2)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_ASSOC_lemma;AND_ASSOC_lemma] THEN
   DISCH_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        ENSURES ((gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))))
            arb_prog";
      "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        UNLESS ((gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))))User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        ENSURES ((gr U2) \/* ((req U1) /\* ((~*(gr U1)) /\*
                            ((req U2) /\* (~*(gr U2)))))))arb_prog /\
       (((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        UNLESS ((gr U2) \/* ((req U1) /\* ((~*(gr U1)) /\*
                           ((req U2) /\* (~*(gr U2)))))))User";
      "(((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        ENSURES ((gr U2) \/* ((req U1) /\* ((~*(gr U1)) /\*
                            ((req U2) /\* (~*(gr U2)))))))User /\
       (((~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))
        UNLESS ((gr U2) \/* ((req U1) /\* ((~*(gr U1)) /\*
                           ((req U2) /\* (~*(gr U2)))))))arb_prog"]
      OR_INTRO_THM1)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "(gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL COMP_ENSURES_thm1)))))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "(gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_thm0)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((~*(req U1)) /\*
         ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) LEADSTO ((gr U2) \/*
         ((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))))))
       (APPEND arb_prog User)";
      "(((req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))) LEADSTO
        (gr U2))(APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)]
    (ISPECL
     ["(~*(req U1)) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";
      "gr U2";
      "(req U1) /\* ((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2))))";"gr U2";
      "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
      LEADSTO_thm28))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_OR_lemma]);;

let sys_live4_lemma5 = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((~*(gr U1)) /\* ((req U2) /\* (~* (gr U2))))
        LEADSTO (gr U2)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live4_lemma3))) THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live4_lemma4))) THEN
   UNDISCH_ALL_TAC THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   UNDISCH_ONE_TAC THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REPEAT DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))) /\* (req U1)) LEADSTO
        (gr U2)) (APPEND arb_prog User)";
      "((((~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))) /\* (~*(req U1)))
        LEADSTO (gr U2)) (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(gr U1)) /\* ((req U2) /\* (~*(gr U2)))";"req U1";"gr U2";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_cor1)) THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let sys_live4_lemma6 = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((~*(gr U1)) /\* (req U2))
        LEADSTO (gr U2)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
      (SPEC_ALL sys_live4_lemma1))) THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live4_lemma5))) THEN
   UNDISCH_ALL_TAC THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   DISCH_TAC THEN
   UNDISCH_TAC "(((req U2) /\* ((gr U2) /\* (~*(gr U1)))) LEADSTO (gr U2))
                  (APPEND arb_prog User)" THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   ONCE_REWRITE_TAC [AND_COMM_AND_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((((~*(gr U1)) /\* (req U2)) /\* (gr U2)) LEADSTO (gr U2))
       (APPEND arb_prog User)";
      "((((~*(gr U1)) /\* (req U2)) /\* (~*(gr U2))) LEADSTO (gr U2))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(~*(gr U1)) /\* (req U2)";"gr U2";"gr U2";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_cor1)));;

%
  Finally we are able to prove:
	req2 --> gr2 in S
%
let sys_live4_lem = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        ((req U2) LEADSTO (gr U2)) (APPEND arb_prog User)"),
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL sys_live3_lem)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL sys_live4_lemma6)) THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   UNDISCH_ALL_TAC THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U2) /\* (gr U1)) LEADSTO (gr U2))(APPEND arb_prog User)";
      "(((req U2) /\* (~*(gr U1))) LEADSTO (gr U2))(APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["req U2";"gr U1";"gr U2";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_cor1)));;

%
  We now turn to the second part of the progress (LEADSTO) proof of the system
  composed of the arb_prog and the specified user.

  This part proves the progress property:

	req1 --> gr1 in S

  To prove this we need to prove some progress properties about the arb_prog
  program that are used in the proof of the progress (LEADSTO) stated above.

  The properties of arb_prog used in the progress (LEADSTO) of the composed
  system are:

     arb_live_tr1b_thm:

	req1 /\ ~gr2			ensures gr1 in A,

     arb_live_tr4a_thm:

	req1 /\ ~gr1 /\ ~req2 /\ gr2	ensures req1 /\ ~gr1 /\ ~gr2 in A,

     arb_live_tr1c_thm:

	req1 /\ ~gr1 /\ ~gr2		ensures gr1 in A

  Let us prove these theorems in the following.
%

%
   To prove these progress properties, we need to prove that the needed ensures
   properties of the given leadsto property holds for the program. This like
   before is a two step proof:
      1) Prove that the unless holds
      2) Prove that a transition validates the property.
   From this the ensures property can be proven.
%

%
  First the safety property.

  Just as before we prove that the unless holds for the program using the
  developed tactic.
%

%
   Prove:
	req1 /\ ~gr2	ensures gr1 in A
%
let arb_safe_tr1b_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) UNLESS (gr U1)) ^arb_prog"),
    PROVE_PROG_TAC);;

let arb_trans_tr1b_lem = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) EXIST_TRANSITION (gr U1)) [^grantleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr1b_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) EXIST_TRANSITION (gr U1)) ^arb_prog"),
   MP_TAC arb_trans_tr1b_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr1b_thm = TAC_PROOF
  (([],
   "(((req U1) /\* (~*(gr U2))) ENSURES (gr U1)) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr1b_thm;arb_trans_tr1b_thm]);;

%
   Prove:
	req1 /\ ~gr1 /\ ~gr2	ensures gr1 in A
%
let arb_safe_tr1c_thm = TAC_PROOF
  (([],
  "(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) UNLESS (gr U1)) ^arb_prog"),
    PROVE_PROG_TAC);;

let arb_trans_tr1c_lem = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) EXIST_TRANSITION (gr U1))
       [^grantleft]"),
   PROVE_PROG_TAC);;

let arb_trans_tr1c_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) EXIST_TRANSITION (gr U1))
      ^arb_prog"),
   MP_TAC arb_trans_tr1c_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr1c_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) ENSURES (gr U1))
      ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr1c_thm;arb_trans_tr1c_thm]);;

%
   Prove:
	req1 /\ ~gr1 /\ ~req2 /\ gr2	ensures req1 /\ ~gr1 /\ ~gr2 in A,
%
let arb_safe_tr4a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((~* (req U2)) /\* (gr U2)))) UNLESS
        ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2))))) ^arb_prog"),
    PROVE_PROG_TAC);;

let arb_trans_tr4a_lem = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((~* (req U2)) /\* (gr U2))))
        EXIST_TRANSITION ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))))
       [^doneright]"),
   PROVE_PROG_TAC);;

let arb_trans_tr4a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((~* (req U2)) /\* (gr U2))))
        EXIST_TRANSITION ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))))
      ^arb_prog"),
   MP_TAC arb_trans_tr4a_lem THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let arb_live_tr4a_thm = TAC_PROOF
  (([],
   "(((req U1) /\* ((~*(gr U1)) /\* ((~* (req U2)) /\* (gr U2)))) ENSURES
        ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2))))) ^arb_prog"),
   REWRITE_TAC [ENSURES;arb_safe_tr4a_thm;arb_trans_tr4a_thm]);;

%
  This ends proving the needed properties of the program.

  Now to the proof of

	sys_live5_thm: req1 --> gr1

  To prove this we may proceed in the following way:

  Prove:
	sys_live5_lem1: req1 /\ ~gr2 --> gr1,

	sys_live5_lem2: req1 /\  gr2 --> gr1,

	   by proving:

		sys_live5_lem2_1: req1 /\  gr1 /\ gr2 --> gr1, weakening

		sys_live5_lem2_2: req1 /\ ~gr1 /\ gr2 --> gr1,

		   by proving:

		      sys_live5_lem2_2_1: req1 /\ ~gr1 /\ ~req2 /\ gr2 --> gr1,

		      sys_live5_lem2_2_2: req1 /\ ~gr1 /\  req2 /\ gr2 --> gr1,
%

%
  The proofs:
%

%
   Prove:
	sys_live5_lem1: req1 /\ ~gr2 --> gr1,
%
let sys_live5_lem1 = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* (~* (gr U2))) LEADSTO (gr U1))(APPEND arb_prog User)"),
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC
    (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] arb_live_tr1b_thm) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U1" (ASSUME
      "!i. ((req i) UNLESS (gr i))User"))) THEN
   ASSUME_TAC (REWRITE_RULE [STABLE] (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. (~*(gr i)) STABLE User")))) THEN
   ASSUME_TAC
    (MP (ISPECL ["(req U1) /\* (~*(gr U2))";"(~*(gr U2)) /\* (gr U1)";"gr U1";
                 "User:^PrTp"] UNLESS_thm3)
        (CONJ (REWRITE_RULE [OR_FALSE_lemma] (ONCE_REWRITE_RULE [OR_COMM_lemma]
               (REWRITE_RULE [AND_FALSE_lemma;OR_FALSE_lemma;P_AND_NOT_P_lemma]
                (MP (ISPECL ["req U1";"gr U1";"~*(gr U2)";
                             "FALSE:^STp->bool";"User:^PrTp"] UNLESS_thm4)
                    (CONJ (ASSUME "((req U1) UNLESS (gr U1))User")
                          (ASSUME "((~*(gr U2)) UNLESS FALSE)User"))))))
              (ISPECL ["~*(gr U2)";"gr U1"] AND_IMPLY_WEAK_lemma))) THEN
   ASSUME_TAC (REWRITE_RULE
    [ASSUME "(((req U1) /\* (~*(gr U2))) ENSURES (gr U1))arb_prog";
     ASSUME "(((req U1) /\* (~*(gr U2))) UNLESS (gr U1))User"] (ISPECL
      ["(req U1) /\* (~*(gr U2))";"gr U1";"arb_prog:^PrTp";"User:^PrTp"]
        (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL COMP_ENSURES_thm1)))))) THEN
   IMP_RES_TAC LEADSTO_thm0);;

%
   Prove:
	sys_live5_lem2_1: req1 /\  gr1 /\ gr2 --> gr1
%
let sys_live5_lem2_1 = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* ((gr U1) /\* (gr U2))) LEADSTO (gr U1))
         (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [APPEND] THEN
   ASSUME_TAC (ISPECL ["(req U1) /\* ((gr U2))";"gr U1"]
                      AND_IMPLY_WEAK_lemma) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((req U1) /\* (gr U2)) /\* (gr U1)";"gr U1";
      "^grantleft";
      "APPEND [^grantright;^doneleft;^doneright] User"]
      LEADSTO_thm25)));;

%
   Prove:
	sys_live5_lem2_2_1: req1 /\ ~gr1 /\ ~req2 /\ gr2 --> gr1,
%
let sys_live5_lem2_2_1 = TAC_PROOF
  (([],
   "!User.
       (IC = ^IC) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2))))
          LEADSTO (gr U1))(APPEND arb_prog User)"),
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC arb_live_tr4a_thm THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC "U1" (UNDISCH_ALL (SPEC_ALL use_safe_lemma1))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. (gr i) STABLE User"))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. ((~*(req i)) UNLESS (~*(gr i)))User"))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((~*(req U2)) UNLESS (~*(gr U2)))User";"((gr U2) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["~*(req U2)";"~*(gr U2)";"gr U2";"FALSE:^STp->bool";"User:^PrTp"]
      UNLESS_thm4)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [AND_FALSE_lemma;OR_FALSE_lemma;P_AND_NOT_P_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* (~*(gr U1))) UNLESS FALSE)User";
      "(((~*(req U2)) /\* (gr U2)) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* (~*(gr U1))";"FALSE:^STp->bool";
      "(~*(req U2)) /\* (gr U2)";"FALSE:^STp->bool";
      "User:^PrTp"]
      UNLESS_thm6)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_FALSE_lemma;AND_ASSOC_lemma] THEN
   DISCH_TAC THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL STABLE))] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))) ENSURES
        ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))))arb_prog";
      "((req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))) STABLE
       User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))";
      "(req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      COMP_UNITY_cor4)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))";
      "(req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_thm0)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. (~*(gr i)) STABLE User"))) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* (~*(gr U1))) UNLESS FALSE)User";
      "((~*(gr U2)) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* (~*(gr U1))";"FALSE:^STp->bool";
      "~*(gr U2)";"FALSE:^STp->bool";"User:^PrTp"]
      UNLESS_thm6)) THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [OR_FALSE_lemma;AND_ASSOC_lemma] THEN
   DISCH_TAC THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL STABLE))] THEN
   DISCH_TAC THEN
   ASSUME_TAC arb_live_tr1c_thm THEN
   UNDISCH_ONE_TAC THEN
   REWRITE_TAC [SYM (ASSUME "arb_prog = ^arb_prog")] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) ENSURES (gr U1))
         arb_prog";
      "((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) STABLE User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))";"gr U1";
      "arb_prog:^PrTp";
      "User:^PrTp"]
      COMP_UNITY_cor4)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))";"gr U1";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_thm0)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))) LEADSTO
        ((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))))(APPEND arb_prog User)";
      "(((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) LEADSTO (gr U1))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))";
      "(req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))";"gr U1";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_thm1)));;


%
   Prove:
	sys_live5_lem2_2_2: req1 /\ ~gr1 /\ gr2 --> gr1,
%

%
  I'm lazy now, we prove a trivial lemma to ease the proving:
%
let sys_live5_lem2_2_2a = TAC_PROOF
  (([],
   "!s. ((((gr U2) /\* (~*(req U2))) /\* (req U1)) /\* (~*(gr U1)))s =
        ((req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2))))s"),
   GEN_TAC THEN
   REWRITE_TAC [/\*;~*] THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

%
  |- (((gr U2) /\* (~*(req U2))) /\* (req U1)) /\* (~*(gr U1)) =
     (req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))
%
let sys_live5_lem2_2_2b = REWRITE_RULE [ETA_AX] (MK_ABS sys_live5_lem2_2_2a);;

let sys_live5_lem2_2_2 = TAC_PROOF
  (([],
   "!User.
     (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* ((~*(gr U1)) /\* (gr U2)))
          LEADSTO (gr U1))(APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem1))) THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem2_2_1))) THEN
   UNDISCH_ALL_TAC THEN
   REWRITE_TAC [use_safe1;use_safe2;use_safe3;use_safe4] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)"))) THEN
   ASSUME_TAC (REWRITE_RULE [STABLE] (SPEC "U1" (UNDISCH_ALL
     (SPEC_ALL use_safe_lemma1)))) THEN
   ASSUME_TAC (REWRITE_RULE [STABLE] (UNDISCH_ALL (SPEC "U2" (ASSUME
      "!i. (gr i) STABLE User")))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* (~*(gr U1))) UNLESS FALSE)User";
      "((gr U2) UNLESS FALSE)User"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL STABLE))]
     (REWRITE_RULE [OR_FALSE_lemma;AND_ASSOC_lemma] (UNDISCH_ALL (ISPECL
        ["(req U1) /\* (~*(gr U1))";"FALSE:^STp->bool";
         "gr U2";"FALSE:^STp->bool";"User:^PrTp"]
         UNLESS_thm6)))) THEN
   ASSUME_TAC (REWRITE_RULE [STABLE;(SYM (ASSUME "arb_prog = ^arb_prog"))]
    (SPEC "U1" arb_safe2_thm)) THEN
   ASSUME_TAC (REWRITE_RULE [NOT_NOT_lemma] (ISPECL
     ["~*(gr U1)";"arb_prog:^PrTp"]
      UNLESS_thm2)) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((req U1) UNLESS FALSE)arb_prog";"((~*(gr U1)) UNLESS (gr U1))arb_prog"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (REWRITE_RULE [OR_FALSE_lemma] (ONCE_REWRITE_RULE [OR_COMM_lemma]
     (UNDISCH_ALL (ISPECL
        ["req U1";"FALSE:^STp->bool";"~*(gr U1)";"gr U1";"arb_prog:^PrTp"]
         UNLESS_thm6)))) THEN
   ASSUME_TAC (ISPECL ["gr U2";"arb_prog:^PrTp"] UNLESS_thm2) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\* (~*(gr U1))) UNLESS (gr U1))arb_prog";
      "((gr U2) UNLESS (~*(gr U2)))arb_prog"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [OR_COMM_lemma]
           (REWRITE_RULE [AND_COMPL_OR_lemma]
           (ONCE_REWRITE_RULE [OR_COMM_OR_lemma]
           (ONCE_REWRITE_RULE [AND_COMM_OR_lemma]
           (ONCE_REWRITE_RULE [OR_COMM_lemma]
           (REWRITE_RULE [AND_ASSOC_lemma]
           (REWRITE_RULE [OR_ASSOC_lemma]
              (UNDISCH_ALL (ISPECL
                 ["(req U1) /\* (~*(gr U1))";"gr U1";"gr U2";"~*(gr U2)";
                  "arb_prog:^PrTp"]
                  UNLESS_thm4))))))))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((req U1) /\* ((~*(gr U1)) /\* (gr U2))) STABLE User";
      "(((req U1) /\* ((~*(gr U1)) /\* (gr U2))) UNLESS
        (((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) \/* (gr U1)))
       arb_prog"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [COMP_UNITY_cor10] (UNDISCH_ALL (ISPECL
     ["(req U1) /\* ((~*(gr U1)) /\* (gr U2))";
      "((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) \/* (gr U1)";
      "User:^PrTp";
      "arb_prog:^PrTp"]
      COMP_UNITY_cor9))) THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((gr U2) LEADSTO (~*(req U2)))(APPEND arb_prog User)";
      "(((req U1) /\* ((~*(gr U1)) /\* (gr U2))) UNLESS
        (((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) \/* (gr U1)))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (REWRITE_RULE [sys_live5_lem2_2_2b]
     (ONCE_REWRITE_RULE [OR_COMM_lemma]
     (REWRITE_RULE [SYM (SPEC_ALL AND_ASSOC_lemma);AND_AND_lemma]
     (ONCE_REWRITE_RULE [AND_COMM_lemma]
       (REWRITE_RULE [SYM (SPEC_ALL AND_ASSOC_lemma)] (UNDISCH_ALL
      (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)] (ISPECL
        ["gr U2";"~*(req U2)";"(req U1) /\* ((~*(gr U1)) /\* (gr U2))";
         "((req U1) /\* ((~*(gr U1)) /\* (~*(gr U2)))) \/* (gr U1)";
         "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
        LEADSTO_thm29)))))))) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [OR_COMM_lemma]
     (REWRITE_RULE [OR_ASSOC_lemma;OR_OR_lemma]
     (UNDISCH_ALL (REWRITE_RULE [CONJ_IMP_THM]
      (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)] (ISPECL
        ["((gr U2) /\* (req U1)) /\* (~*(gr U1))";
         "(((~*(gr U2)) /\* (req U1)) /\* (~*(gr U1))) \/* (gr U1)";
         "(req U1) /\* ((~*(gr U1)) /\* ((~*(req U2)) /\* (gr U2)))";"gr U1";
         "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
         LEADSTO_thm28)))))) THEN
   ASSUME_TAC (MP
    (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)] (ISPECL
     ["~*(gr U2) /\* (req U1)";"gr U1";"~*(gr U1)";
      "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
      LEADSTO_cor8)) (ONCE_REWRITE_RULE [AND_COMM_lemma] (UNDISCH_ALL
                      (REWRITE_RULE [CONJ_IMP_THM;use_safe1;use_safe2;
                                     use_safe3;use_safe4]
                    (SPEC_ALL sys_live5_lem1))))) THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [AND_AND_COMM_lemma]
     (REWRITE_RULE [AND_ASSOC_lemma] (ONCE_REWRITE_RULE [AND_COMM_AND_lemma]
     (REWRITE_RULE [OR_OR_lemma] (UNDISCH_ALL
     (REWRITE_RULE [CONJ_IMP_THM]
      (REWRITE_RULE [UNDISCH (SPEC_ALL sys_live1_lem_1)] (ISPECL
       ["((gr U2) /\* (req U1)) /\* (~*(gr U1))";"gr U1";
        "((~*(gr U2)) /\* (req U1)) /\* (~*(gr U1))";"gr U1";
        "st:^STp->^STp";"APPEND (arb_prog':^PrTp) User"]
        LEADSTO_thm28)))))))) THEN
   ASM_REWRITE_TAC []);;

%
   Prove:
	sys_live5_lem2: req1 /\  gr2 --> gr1,
%
let sys_live5_lem2 = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (((req U1) /\* (gr U2)) LEADSTO (gr U1)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem2_1))) THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   DISCH_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem2_2_2))) THEN
   UNDISCH_ONE_TAC THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   DISCH_TAC THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["((((req U1) /\* (gr U2)) /\* (gr U1)) LEADSTO (gr U1))
       (APPEND arb_prog User)";
      "((((req U1) /\* (gr U2)) /\* (~*(gr U1))) LEADSTO (gr U1))
       (APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(req U1) /\* (gr U2)";"gr U1";"gr U1";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_cor1)));;

%
   Prove:
	sys_live5_thm: req1 --> gr1
%
let sys_live5_thm = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        ((req U1) LEADSTO (gr U1)) (APPEND arb_prog User)"),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem1))) THEN
   ASSUME_TAC (REWRITE_RULE [SYM (ASSUME "arb_prog = ^arb_prog")] (REWRITE_RULE
    [ASSUME "IC = ^IC";ASSUME "(CONS st arb_prog') = (arb_prog:^PrTp)";
     ASSUME "arb_prog = ^arb_prog";
     ASSUME "use_safe1 User IC";ASSUME "use_safe2 User IC";
     ASSUME "use_safe3 User IC";ASSUME "use_safe4 User IC";
     ASSUME "(!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User))"]
       (SPEC_ALL sys_live5_lem2))) THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["(((req U1) /\*     (gr U2)) LEADSTO (gr U1))(APPEND arb_prog User)";
      "(((req U1) /\* (~*(gr U2))) LEADSTO (gr U1))(APPEND arb_prog User)"]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (ISPECL
     ["req U1";"gr U2";"gr U1";
      "APPEND arb_prog User:^PrTp"]
      LEADSTO_cor1)));;

%
   Finally we prove:
	sys_live_thm: !i. req(i) --> gr(i) in S
%
let sys_live_thm = TAC_PROOF
  (([],
   "!User.
      (IC = ^IC) /\ (CONS st arb_prog' = arb_prog) /\ (arb_prog = ^arb_prog) /\
       use_safe1 User IC /\ use_safe2 User IC /\
       use_safe3 User IC /\ use_safe4 User IC /\
       (!(i:user). ((gr i) LEADSTO (~*(req i)))(APPEND arb_prog User)) ==>
        (!i:user. ((req i) LEADSTO (gr i)) (APPEND arb_prog User))"),
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL sys_live4_lem)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL sys_live5_thm)) THEN
   user_INDUCT_TAC THEN ASM_REWRITE_TAC []);;

%
  End of example
%

% close_theory( );; %
