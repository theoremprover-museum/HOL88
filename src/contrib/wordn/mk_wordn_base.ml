% ===================================================================== %
% FILE		: mk_wordn_base.ml					%
% DESCRIPTION   : Creates the theory "wordn_base.th".			%
% WRITES FILES	: wordn_base.th						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 90.08.20					        %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory							%
% --------------------------------------------------------------------- %
new_theory `wordn_base`;;

% --------------------------------------------------------------------- %
% The defining property of WORDn and BITSn for any n.                   %
% --------------------------------------------------------------------- %
let wordn_ABS_REP =
    prove_thm
    (`wordn_ABS_REP`,
     "!n. (?rep:*->(bool)list. TYPE_DEFINITION(\l'. LENGTH l' = n)rep)
           ==>
          ?REP. ?ABS:(bool)list->*. 
          (!w:*. ABS(REP w) = w) /\ !l. (LENGTH l = n) = (REP(ABS l) = l)",
     GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP ABS_REP_THM) THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_ACCEPT_TAC);;

% --------------------------------------------------------------------- %
% The theorem for defining functions on wordn types.			%
% --------------------------------------------------------------------- %
let wordn_FN_DEF_THM = 
    prove_thm
    (`wordn_FN_DEF_THM`,
     "!n. !ABS. !REP.
      ((!a:*a. ABS(REP a) = a) /\ 
       (!r:(bool)list. (LENGTH r = n) = (REP(ABS r:*a) = r))) ==>
      !f. ?!fn. !r:(bool)list. (LENGTH r = n) ==> (fn (ABS r):* = f r)",
    CONV_TAC (ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CONJ_TAC THENL
    [EXISTS_TAC "\x:*a.(f:(bool)list->*) (REP x)" THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     REPEAT STRIP_TAC THEN AP_TERM_TAC THEN RES_TAC;
     REPEAT GEN_TAC THEN
     CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV "x:*a")) THEN
     DISCH_THEN (\th. GEN_TAC THEN MP_TAC th) THEN
     DISCH_THEN (STRIP_THM_THEN (MP_TAC o SPEC "REP (x:*a):(bool)list")) THEN
     ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC]);;

% --------------------------------------------------------------------- %
% For use in type definition package...					%
% --------------------------------------------------------------------- %
let EXISTS_wordn_REP = 
    prove_thm
    (`EXISTS_wordn_REP`,
     "!n. ?l:(bool)list. (\l. LENGTH l = n) l",
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     INDUCT_THEN INDUCTION STRIP_ASSUME_TAC THENL
     [EXISTS_TAC "[]:bool list";EXISTS_TAC "CONS T l"] THEN
     ASM_REWRITE_TAC [LENGTH]);;

% --------------------------------------------------------------------- %
% Close the theory					                %
% --------------------------------------------------------------------- %
close_theory();;
