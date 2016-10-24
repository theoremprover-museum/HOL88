% ===================================================================== %
% HOL TRAINING COURSE: a proof about the predicate NEXT.		%
% ===================================================================== %

% ===================================================================== %
% We need to create a new theory, since we will be making a definition.	%
% ===================================================================== %

new_theory `next`;;

% ===================================================================== %
% Here is the definition of a predicate NEXT.  NEXT (t1,t2) P says that %
% the next time after t1 that P is true is t2.				%
% ===================================================================== %
let NEXT =
 new_definition
  (`NEXT`, 
   "!P t1 t2. 
     NEXT (t1,t2) P =
      (t1 < t2) /\ (P t2)  /\ (!t. (t1 < t) /\ (t < t2) ==> ~P t)");;

% ===================================================================== %
% Prove the following lemma for increasing the size of the time		%
% interval covered by the predicate NEXT:				%
%									%
%   |- !P t1 t2. ~P(SUC t1) /\ NEXT(SUC t1,t2)P ==> NEXT(t1,t2)P	%
% ===================================================================== %

let NEXT_INCR = 
    prove_thm
    (`NEXT_INCR`,
     "!P t1 t2. ~P(SUC(t1)) /\ NEXT(SUC(t1),t2)P  ==> NEXT(t1,t2)P",
     PURE_ONCE_REWRITE_TAC [NEXT] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] OR_LESS);
      ASM_REWRITE_TAC [];
      let th = UNDISCH (SPECL ["t1:num";"t:num"] LESS_OR) in
      DISJ_CASES_TAC (PURE_ONCE_REWRITE_RULE [LESS_OR_EQ] th) THENL
      [RES_TAC; FIRST_ASSUM (\th g. SUBST_ALL_TAC th g) THEN RES_TAC]]);;


% ===================================================================== %
% Prove the following lemma for decreasing the size of the time 	%
% interval covered by the predicate NEXT:				%
%									%
%   |- !P t1 t2. NEXT (t1,t2) P /\ ~P(SUC t1) ==> NEXT (SUC t1,t2) P	%
% ===================================================================== %

let NEXT_DECR =
    prove_thm
    (`NEXT_DECR`,
     "!P t1 t2. NEXT (t1,t2) P /\ ~P(SUC t1) ==> NEXT (SUC t1,t2) P",
     PURE_ONCE_REWRITE_TAC [NEXT] THEN
     REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LESS_NOT_SUC THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RES_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      IMP_RES_TAC SUC_LESS THEN RES_TAC]);;



