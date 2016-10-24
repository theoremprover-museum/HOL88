
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         mult.ml                                                    %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION : Theorems about MULT and EXP		     		     %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Elsa L Gunter							     %
%   Philippe Leveilley							     %
%   Wim Ploegaerts							     %
%   Wai Wong                                                                 %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%    New theorems added:                                                     %
%           EXP1                                                             %
%           ZERO_LESS_TWO_EXP                                                %
%           ONE_LESS_EQ_TWO_EXP                                              %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%     Removed dependencies on several external files/theories                %
%     Added extra theorems by Wai Wong                                       %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%****************************************************************************%
%                                                                            %
%  DEPENDANCIES :                                                            %
%                                                                            %
%****************************************************************************%

system `rm -f mult.th`;;

new_theory `mult`;;

% PC 22-4-92 These are no longer used%
%new_parent `ineq`;;%
%loadf (library_pathname() ^ `/group/start_groups`);;%
%loadf `tools`;;%
%autoload_defs_and_thms `ineq`;;%

%<-------------------------------------------------------------------------->%

%<PL>%
let LESS_MONO_MULT1 =
    save_thm (`LESS_MONO_MULT1`,
	      GEN_ALL
		(SUBS [SPECL ["m:num";"p:num"] MULT_SYM;
		       SPECL ["n:num";"p:num"] MULT_SYM]
		      (SPEC_ALL LESS_MONO_MULT)));;

%============================================================================%
%									     %
% 		       Inequalities and multiplication			     %
%									     %
%============================================================================%

%WP 4-9-90%

let LESS_MULT_PLUS_DIFF = prove_thm (
  `LESS_MULT_PLUS_DIFF`,
   "!n k l . (k < l) ==> (((k * n) + n) <= (l * n))",
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;LESS_EQ_REFL] THEN
  DISCH_THEN \t . 
    REPEAT GEN_TAC THEN
    DISCH_THEN \t'.
         ACCEPT_TAC 
         (REWRITE_RULE [ADD_CLAUSES;ADD_ASSOC]
           (MATCH_MP LESS_EQ_LESS_EQ_MONO
             (CONJ (MATCH_MP LESS_OR t') (MATCH_MP t t'))))
);;

%<-------------------------------------------------------------------------->%

%<ELG>%
% Moved to main system by RJB on 92.10.08 %
%let LEFT_SUB_DISTRIB = save_thm (`LEFT_SUB_DISTRIB`,%
%((SPECL["n:num";"p:num";"m:num"] RIGHT_SUB_DISTRIB) and_then%
% (PURE_ONCE_REWRITE_RULE[MULT_SYM]) and_then%
% (GENL["m:num";"n:num";"p:num"])));;%

%LEFT_SUB_DISTRIB = 
 |- !m:num n:num p:num. m * (n - p) = (m * n) - (m * p)%


%----------------------------------------------------------------------------%
% ONE_LESS_TWO_EXP_SUC = |- !n. 1 < (2 EXP (SUC n))                          %
%----------------------------------------------------------------------------%
%<RJB>%
let ONE_LESS_TWO_EXP_SUC =
 prove_thm
  (`ONE_LESS_TWO_EXP_SUC`,
   "!n. 1 < (2 EXP (SUC n))",
   INDUCT_TAC THENL
   [REWRITE_TAC [EXP] THEN
    REWRITE_TAC [num_CONV "2";MULT_CLAUSES] THEN
    REWRITE_TAC [LESS_SUC_REFL];
    PURE_ONCE_REWRITE_TAC [EXP] THEN
    REWRITE_TAC [TIMES2] THEN
    ASSUME_TAC (SPEC "2 EXP (SUC n)" (SPEC "2 EXP (SUC n)" LESS_EQ_ADD)) THEN
% PC 12/8/92 CONJUNCT2 LESS_EQ_LESS_TRANS -> LESS_LESS_EQ_TRANS %
%    IMP_RES_TAC LESS_EQ_LESS_TRANS]);;%
    IMP_RES_TAC LESS_LESS_EQ_TRANS]);;

%****************************************************************************%
%                                                                            %
% AUTHOR        : Wai Wong                                                   %
% DATE          : April 1993                                                 %
%                                                                            %
%****************************************************************************%

let NOT_MULT_LESS_0 = prove_thm(`NOT_MULT_LESS_0`,
    "!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)",
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES;LESS_0]);;

let EXP1 = prove_thm(`EXP1`, "!n. n EXP 1 = n",
    CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[EXP;MULT_CLAUSES]);;

let ZERO_LESS_TWO_EXP = save_thm(`ZERO_LESS_TWO_EXP`,% |- !n. 0 < (2 EXP n) %
    GEN_ALL (SUBS[SYM (num_CONV "2")](SPECL ["n:num"; "1"] ZERO_LESS_EXP)));;

let ONE_LESS_EQ_TWO_EXP = prove_thm(`ONE_LESS_EQ_TWO_EXP`,
    "!n. 1 <= (2 EXP n)",
    INDUCT_TAC THENL[
     REWRITE_TAC[EXP;LESS_EQ_REFL];
     REWRITE_TAC[LESS_OR_EQ] THEN DISJ1_TAC
     THEN MATCH_ACCEPT_TAC ONE_LESS_TWO_EXP_SUC]);;

close_theory();;
