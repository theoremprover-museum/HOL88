
new_theory `dynamic_logic`;;

load_library `string`;;
new_parent `halts_logic`;;
new_parent `dijkstra`;;

let Box =
 new_definition
  (`Box`,
   "Box c p (s:state) = !s':state. c(s,s') ==> p s'");;

let Diamond =
 new_definition
  (`Diamond`,
   "Diamond c p s = ~Box c (\s. ~(p s)) s");;

let Valid =
 new_definition
  (`Valid`,
   "Valid p = !s:state. p s");;

load_theorems `halts`;;
load_theorems `hoare_thms`;;
load_theorems `dijkstra`;;
load_definition `halts` `HALTS`;;
load_definition `semantics` `MK_SPEC`;;l
load_definition `semantics` `DET`;;l
load_definition `halts_thms` `T_SPEC`;;


% Useful functions for interactive proof
  (should be in the system).
%

let Box_MK_SPEC =
 prove_thm
  (`Box_MK_SPEC`,
   "Valid(Box c p) = MK_SPEC((\s. T),c,p)",
   REWRITE_TAC[Valid;Box;MK_SPEC]);;

load_library `taut`;;

let IMP_LEMMA = TAUT_PROVE  "!t1 t2. ~(t1 ==> ~t2) = (t1 /\ t2)";;

% Following proof modified for new RES_TAC                  [TFM 90.06.14] %

let Diamond_HALTS =
 prove_thm
  (`Diamond_HALTS`,
   "DET c ==> (Valid(Diamond c p) = T_SPEC((\s. T),c,p))",
   REWRITE_TAC[Valid;Box;Diamond;MK_SPEC;T_SPEC;HALTS;DET]
    THEN BETA_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[IMP_LEMMA]
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [ASSUM_LIST (\thl. STRIP_ASSUME_TAC (SPEC "s1:state" (el 2 thl))) THEN
      RES_TAC THEN SUBST1_TAC (ASSUME "s2:state = s'") THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASSUM_LIST (\thl. STRIP_ASSUME_TAC (SPEC "s:state" (el 1 thl))) THEN
      EXISTS_TAC "s':state" THEN FIRST_ASSUM ACCEPT_TAC;
      ASSUM_LIST (\thl. STRIP_ASSUME_TAC (SPEC "s:state" (el 1 thl))) THEN
      RES_TAC THEN EXISTS_TAC "s':state" THEN
     CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

% Following proof modified for new RES_TAC                  [TFM 90.06.14] %

let Diamond_WP =
 prove_thm
  (`Diamond_WP`,
   "DET c ==> (WP(c,q) s = Diamond c q s)",
   REWRITE_TAC[Diamond;Box;WP_THM;DET]
    THEN BETA_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[IMP_LEMMA]
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
     [EXISTS_TAC "s':state" THEN STRIP_TAC THEN
      RES_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REPEAT STRIP_TAC THENL
        [EXISTS_TAC "s':state" THEN FIRST_ASSUM ACCEPT_TAC;
         RES_TAC THEN SUBST1_TAC (ASSUME "s'':state = s'") THEN
         FIRST_ASSUM ACCEPT_TAC]]);;

let --> =
 new_infix_definition
  (`-->`,
   "$--> p q = \s:state. p s ==> q s");;

let Box_MK_SPEC1 =
 prove_thm
  (`Box_MK_SPEC1`,
   "Valid(p --> Box c q) = MK_SPEC(p,c,q)",
   REWRITE_TAC[Valid;Box;MK_SPEC;-->]
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC);;

let Diamond_HALTS1 =
 prove_thm
  (`Diamond_HALTS1`,
   "DET c ==> (Valid(p --> (Diamond c q)) = T_SPEC(p,c,q))",
   REWRITE_TAC[Valid;Box;Diamond;MK_SPEC;T_SPEC;HALTS;DET;-->]
    THEN BETA_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[IMP_LEMMA]
    THEN STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [RES_TAC THEN
       SUBST1_TAC (ASSUME "s2:state = s'") THEN
       FIRST_ASSUM ACCEPT_TAC;
      RES_TAC THEN EXISTS_TAC "s':state" THEN
       FIRST_ASSUM ACCEPT_TAC;
      RES_TAC THEN EXISTS_TAC "s':state" THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let DET_THM =
 prove_thm
  (`DET_THM`,
   "!c q. DET c ==> Valid(Diamond c q --> Box c q)",
   REWRITE_TAC[DET;Valid;Box;Diamond;-->]
    THEN BETA_TAC
    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
    THEN REWRITE_TAC[IMP_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASSUM_LIST(\thl. REWRITE_TAC[el 3 thl])
    THEN ASM_REWRITE_TAC[]);;

