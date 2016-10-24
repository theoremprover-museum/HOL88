
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         suc.ml                                                     %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION   : Theorems about SUC                   		     %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Richard J.Boulton							     %
%   Rachel Cardell-Oliver						     %
%   Paul Curzon							 	     %
%   Jeff Joyce 							             %
%   Philippe Leveilley							     %
%   Wim Ploegaerts							     %
%                                                                            %
%****************************************************************************%
%                                                                            %
%  PC 5/7/92      NOT_SUC_LESS_EQ -->    NOT_FORALL_SUC_LESS_EQ              %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 21/4/93                                                                 %
%     Removed dependencies on several external files/theories                %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%****************************************************************************%
%                                                                            %
%  DEPENDANCIES :                                                            %
%                                                                            %
%                                                                            %
%****************************************************************************%

system `rm -f suc.th`;;

new_theory `suc`;;

% PC 22-4-92 These are no longer used%
%new_parent `ineq`;;%
%loadf `tools`;;%
%autoload_defs_and_thms `ineq`;;%


%<-------------------------------------------------------------------------->%

%<PL>%
% Moved to main system by RJB on 92.09.28 %
%let NOT_SUC_LESS_EQ_0 =%
%    prove_thm (`NOT_SUC_LESS_EQ_0`,%
%               "! n . ~ (SUC n) <= 0",%
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%	       REWRITE_TAC[NOT_LESS_EQ_LESS;LESS_0]);;%
%  	       REWRITE_TAC[NOT_LESS_EQUAL;LESS_0]);;%

%<-------------------------------------------------------------------------->%

%<PL>%
% Name changed from NOT_SUC_LESS_EQ to avoid clash. PC 5/7/92 %
let NOT_FORALL_SUC_LESS_EQ =
    save_thm (`NOT_FORALL_SUC_LESS_EQ`,
	      NOT_INTRO
	       (DISCH_ALL
		 (REWRITE_RULE [NOT_SUC_LESS_EQ_0]
	                       (SPEC "0" (ASSUME "(!n m. (SUC m) <= n)")))));;
	 

%<-------------------------------------------------------------------------->%



% NOT_0_GREATER_EQ_SUC |- ~0 >= (SUC n)%

let NOT_0_GREATER_EQ_SUC = save_thm(`NOT_0_GREATER_EQ_SUC`,
  GEN_ALL
   (REWRITE_RULE[LESS_0;GSYM GREATER_EQ]
     (SPEC "SUC n" (SPEC "0" LESS_EQ_ANTISYM))));;



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%SUC_GREATER_EQ_SUC = |- !m n. (SUC m) >= (SUC n) = m >= n %

let  SUC_GREATER_EQ_SUC = save_thm (`SUC_GREATER_EQ_SUC`,
       REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO);;



%****************************************************************************%
%                                                                            %
% AUTHOR        : R.J.Boulton                                                %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%

%----------------------------------------------------------------------------%
% LESS_EQ_MONO_EQ = |- !m n. (SUC m) <= (SUC n) = m <= n                     %
%----------------------------------------------------------------------------%

let LESS_EQ_MONO_EQ = LESS_EQ_MONO;;

%----------------------------------------------------------------------------%
% LESS_EQ_LESS_SUC = |- !m n. m <= n = m < (SUC n)                           %
%----------------------------------------------------------------------------%

let LESS_EQ_LESS_SUC =
 prove_thm
  (`LESS_EQ_LESS_SUC`,
   "!m n. (m <= n) = (m < (SUC n))",
   REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THENL
    [IMP_RES_TAC LESS_SUC;
     ASM_REWRITE_TAC [LESS_SUC_REFL]];
    REWRITE_TAC [LESS_THM] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);;
%----------------------------------------------------------------------------%
let SUC_LESS_EQ =  prove_thm(`SUC_LESS_EQ`,
  "!m n. ((m <= n) /\ ~(m = n)) ==> (SUC m) <= n",
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC "m <= n" THEN
   SUBST_TAC [SPEC_ALL LESS_OR_EQ] THEN
   ASM_REWRITE_TAC [LESS_EQ]);;
%----------------------------------------------------------------------------%

let NOT_SUC_LESS_EQ_SELF = prove_thm(`NOT_SUC_LESS_EQ_SELF`,
  "!n. ~((SUC n) <= n)",
   GEN_TAC THEN
   REWRITE_TAC [LESS_OR_EQ;DE_MORGAN_THM] THEN
   REWRITE_TAC [SUC_ID;NOT_LESS;LESS_EQ_SUC_REFL]);;
%----------------------------------------------------------------------------%


%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%


let SUC_0=prove_thm(`SUC_0`,
 "1 = (SUC 0)",
 ASM_REWRITE_TAC[ADD1;ADD_CLAUSES]);;



let SUC_NOT_0 = save_thm(`SUC_NOT_0`, GSYM SUC_NOT);;


close_theory();;
