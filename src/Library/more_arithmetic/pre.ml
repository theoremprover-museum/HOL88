
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         pre.ml                                                     %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION   : Theorems about PRE		     		             %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Rachel Cardell-Oliver						     %
%   Wim Ploegaerts							     %
%   Wai Wong                                                                 %
%                                                                            %
%****************************************************************************%
%                                                                            %
% PC 12/8/92                                                                 %
%   The tactic for PRE_MONO_LESS_EQ has been changed to remove the           %
%   dependancy on the auxiliary library                                      %
%                                                                            %
% PC 21/4/93                                                                 %
%    New theorem added:  LESS_IMP_LESS_EQ_PRE                                %
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
%                                                                            %
%****************************************************************************%


system `rm -f pre.th`;;

new_theory `pre`;;

% PC 12/8/92 %
%load_library `auxiliary`;;%

% PC 22-4-92 These are no longer used%
%loadf (library_pathname() ^ `/group/start_groups`);;%
%new_parent `ineq`;;%
%loadf `tools`;;%
%autoload_defs_and_thms `ineq`;;%





%============================================================================%
%									     %
% 			  Theorems dealing with PRE			     %
%									     %
%============================================================================%

%<WP>%
%New proof by PC 22-4-93%
let SUC_PRE = prove_thm (
  `SUC_PRE`,
  "!n . (0 < n) ==> ((SUC (PRE n)) = n)",
  REPEAT STRIP_TAC THEN
  (ACCEPT_TAC
       (REWRITE_RULE[]
          (MATCH_MP (SPECL["PRE n";"n:num"] PRE_SUC_EQ)
                 (ASSUME "0 < n") )))
);;

%  IMP_RES_TAC (SPEC "PRE n" PRE_SUC_EQ) THEN%
%  FIRST_ASSUM (\thm . SUBST_MATCH_TAC (GSYM thm) ? NO_TAC ) THEN%
%  REFL_TAC%
%);;%

%<-------------------------------------------------------------------------->%

%<WP>%
let PRE_MONO = prove_thm  (
  `PRE_MONO`,
  "! m n . (PRE m < PRE n) ==> (m < n)",
  INDUCT_TAC THEN
  INDUCT_TAC  THEN
  REWRITE_TAC [PRE;NOT_LESS_0;LESS_0;LESS_MONO]
);;

%<-------------------------------------------------------------------------->%

%<WP>%
let PRE_MONO_LESS_EQ = prove_thm (
 `PRE_MONO_LESS_EQ`,
 "! m n . (m < n) ==> (PRE m <= PRE n)",
% PC 12/8/92  Changed to remove the dependancy on the auxiliary library %
%  (2 TIMES INDUCT_TAC) THEN %
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0;PRE;LESS_MONO_EQ;ZERO_LESS_EQ] THEN
  DISCH_THEN \thm . REWRITE_TAC [LESS_OR_EQ;thm]
);;

%<-------------------------------------------------------------------------->%

%<WP>%
%< PRE_LESS_EQ = |- !n. (PRE n) <= n >%

let PRE_LESS_EQ =  save_thm (
          `PRE_LESS_EQ`, 
          GEN_ALL (REWRITE_RULE [PRE]
                     (MATCH_MP PRE_MONO_LESS_EQ (SPEC "n:num" LESS_SUC_REFL)))
);;

%<-------------------------------------------------------------------------->%

%<WP>%
let PRE_ADD = prove_thm  (
  `PRE_ADD`,
  "!n m . (0 < n) ==> (PRE ( n + m ) = (PRE n) + m)",
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0;PRE;ADD_CLAUSES]
);;


%============================================================================%
%									     %
% 			     relation SUC / PRE				     %
%									     %
%============================================================================%




%<WP>%
let SUC_LESS_PRE = prove_thm (
  `SUC_LESS_PRE`,
  "! m n . (SUC m < n) ==> (m < PRE n)",
  GEN_TAC THEN 
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0;PRE;LESS_MONO_EQ]
);;

%<-------------------------------------------------------------------------->%

%<WP>%
let SUC_LESS_EQ_PRE = prove_thm  (
  `SUC_LESS_EQ_PRE`,
  "! m n . (0 < n) ==> (SUC m <= n) ==> (m <= PRE n)",
  REPEAT GEN_TAC THEN
  DISCH_THEN \thm . REWRITE_TAC [LESS_OR_EQ;MATCH_MP PRE_SUC_EQ thm] THEN
  STRIP_TAC THEN
  IMP_RES_TAC SUC_LESS_PRE THEN
  ASM_REWRITE_TAC []
);;

%<-------------------------------------------------------------------------->%

%<WP>%
let PRE_K_K = prove_thm (
  `PRE_K_K`,
  "!k . (0<k) ==> (PRE k < k)",
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [LESS_REFL;LESS_0;PRE;LESS_SUC_REFL] 
);;

%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%

let NOT_LESS_SUB = PROVE
  ("!m n. ~( m < (m-n) )"  ,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC "m<=n" THENL
   [ POP_ASSUM(\thm. REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0]thm;NOT_LESS_0]);
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
%     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQ_LESS]) THEN %
     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQUAL]) THEN
     IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
     IMP_RES_TAC SUB_ADD THEN
     REWRITE_TAC[NOT_LESS] THEN
     ONCE_REWRITE_TAC[GSYM(SPECL["m-n";"m:num";"n:num"]LESS_EQ_MONO_ADD_EQ)]
     THEN ASM_REWRITE_TAC[LESS_EQ_ADD] ] );;




let PRE_LESS = prove_thm(`PRE_LESS`,
  "!b:num. ( (0<b) /\ (b<a) ==> ((PRE b) < a))",
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE [NOT_LESS]
     (SPECL ["b:num";"1"] NOT_LESS_SUB)) THEN
  IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
  ASM_REWRITE_TAC[PRE_SUB1] );;


%****************************************************************************%
%                                                                            %
% AUTHOR        : Wai Wong                                                   %
% DATE          : April 1993                                                 %
%                                                                            %
%****************************************************************************%


let LESS_IMP_LESS_EQ_PRE = prove_thm(`LESS_IMP_LESS_EQ_PRE`,
    "!m n. 0 < n ==> ((m < n) = (m <= (PRE n)))",
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
     DISCH_TAC THEN REWRITE_TAC[PRE;ZERO_LESS_EQ;LESS_0];
     REWRITE_TAC[PRE;LESS_MONO_EQ] THEN STRIP_TAC
     THEN MATCH_ACCEPT_TAC LESS_EQ]);;



close_theory();;
