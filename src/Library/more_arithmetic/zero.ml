
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         zero_ineq.ml                                               %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         July 1991                                                  %
%   DESCRIPTION:  Inequalities about 0		     		     	     %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theories of 				     %
%                                                                            %
%   Mike Benjamin							     %
%   Rachel Cardell-Oliver						     %
%   Paul Curzon							 	     %
%   Wim Ploegaerts							     %
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

system `rm -f zero_ineq.th`;;

new_theory `zero_ineq`;;

% PC 22-4-92 These are no longer used%
%new_parent `ineq`;;%
%loadf `tools`;;%
%autoload_defs_and_thms `ineq`;;%

let autoload_defs_and_thms thy =
   map (\name. autoload_theory(`definition`,thy,name))
     (map fst (definitions thy));
   map (\name. autoload_theory(`theorem`,thy,name))
     (map fst (theorems thy)) in

   autoload_defs_and_thms `prim_rec`;;




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Wim Ploegaerts                                             %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%WP 4-9-90%
let M_LESS_0_LESS = prove_thm  (
  `M_LESS_0_LESS`,
  "! m n . (m < n) ==> (0 < n)",
  REPEAT GEN_TAC THEN
  DISCH_THEN \thm . ASSUME_TAC
% PC 12/8/92 CONJ1 LESS_EQ_LESS_TRANS -> LESS_EQ_LESS_TRANS %
%               (MATCH_MP (CONJ1 LESS_EQ_LESS_TRANS)%
               (MATCH_MP (LESS_EQ_LESS_TRANS)
                         (CONJ (SPEC "m:num" ZERO_LESS_EQ) thm)) THEN
  FIRST_ASSUM ACCEPT_TAC
);;
 
%<-------------------------------------------------------------------------->%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Paul Curzon                                                %
%   DATE:         June 1991                                                  %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

let LESS1EQ0 = prove_thm (`LESS1EQ0`,
       "!m . (m < 1) = (m = 0)",

 GEN_TAC THEN
 EQ_TAC THENL[

 (CONV_TAC (DEPTH_CONV num_CONV)) THEN
 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[REWRITE_RULE
                      [ASSUME "m < (SUC 0)"; NOT_LESS_0]
                      (SPECL ["m:num";"0"] LESS_LEMMA1)]);

 DISCH_TAC THEN
 (REWRITE_TAC[ASSUME "m = 0"]) THEN
 (CONV_TAC (DEPTH_CONV num_CONV)) THEN
 (REWRITE_TAC[LESS_SUC_REFL])]);;

% (POP_ASSUM (\th . ASSUME_TAC (REWRITE_RULE[th]%
%                      (SPECL ["m:num";"0"] LESS_LEMMA1)))) THEN%
% (POP_TAC (REWRITE_RULE[NOT_LESS_0])) THEN%
% POP_REWRITE_TAC;%
% DISCH_TAC THEN%
% POP_REWRITE_TAC THEN%
% (CONV_TAC (DEPTH_CONV num_CONV)) THEN%
% (REWRITE_TAC[LESS_SUC_REFL])]);;%
%<-------------------------------------------------------------------------->%
let NOT_EQ_0 = prove_thm(`NOT_EQ_0`,
   "! m . ~ ( m = 0)  ==> (m >= 1)",
 INDUCT_TAC THENL
 [
 (REWRITE_TAC[]);

 (REPEAT STRIP_TAC) THEN
 (ASM_CASES_TAC "m = 0") THENL
   [
    REWRITE_TAC[ASSUME "m = 0"] THEN
%    POP_REWRITE_TAC THEN%
    (CONV_TAC (ONCE_DEPTH_CONV num_CONV)) THEN
    (REWRITE_TAC[LESS_EQ_REFL;GREATER_EQ]);

    (REWRITE_TAC[GREATER_EQ;ADD1]) THEN
    (ONCE_REWRITE_TAC[ADD_SYM]) THEN
    (REWRITE_TAC[LESS_EQ_ADD])
   ]
 ]
);;

%<-------------------------------------------------------------------------->%
let LESS_EQ_0_EQ = prove_thm(`LESS_EQ_0_EQ`,
"!m. m <= 0 ==> (m = 0)",
 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC [LESS_OR_EQ;
              (REWRITE_RULE[ASSUME "m <= 0"]
                           (SPEC_ALL 
                             (REWRITE_RULE[GSYM NOT_LESS_EQUAL]
                                          LESS_0_CASES)) )]));;
% (REPEAT STRIP_TAC) THEN%
% (REWRITE_TAC [LESS_OR_EQ]) THEN%
% (ASSUME_TAC (SPEC_ALL (REWRITE_RULE[GSYM NOT_LESS_EQ_LESS] LESS_0_CASES))) THEN %
% PC 12/8/92 NOT_LESS_EQ_LESS -> NOT_LESS_EQUAL %
% (ASSUME_TAC (SPEC_ALL (REWRITE_RULE[GSYM NOT_LESS_EQUAL] LESS_0_CASES))) THEN%
% (REWRITE_A1_WITH_A2_THEN ASSUME_TAC) THEN%
% (ASM_REWRITE_TAC[]));;%

%<-------------------------------------------------------------------------->%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   AUTHOR:       Mike Benjamin                                              %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   ***************************************************************************
    *                                                                         *
    *    If a number is greater than zero then it's not zero.                 *
    *                                                                         *
    *    GREATER_NOT_ZERO = |- !x. 0 < x ==> ~(x = 0)                         *
    *                                                                         *
    **************************************************************************%

%let GREATER_NOT_ZERO = prove_thm (`GREATER_NOT_ZERO`,%
%"! (x:num). (0 < x) ==> ~(x = 0)",%
%GEN_TAC%
%THEN CUT_THM_TAC (SPEC "x:num" num_CASES)%
%THEN DISJ_LEFT_TAC%
%THENL [%
% ASM_REWRITE_TAC [LESS_REFL];%
% EXISTS_LEFT_TAC%
% THEN ASM_REWRITE_TAC []%
% THEN DISCH_TAC%
% THEN IMP_RES_TAC (SPEC "SUC (n:num)" (SPEC "0" LESS_NOT_EQ))%
% THEN N_REVERSE_TAC 1%
% THEN N_REWRITE_TAC 1]);;%

%New proof by PC 22-4-93%
let GREATER_NOT_ZERO = prove_thm (`GREATER_NOT_ZERO`,
"! (x:num). (0 < x) ==> ~(x = 0)",
 (REPEAT STRIP_TAC) THEN
 UNDISCH_TAC "0<x" THEN
 ASM_REWRITE_TAC[LESS_REFL]);;


%****************************************************************************%
%                                                                            %
% AUTHOR        : Rachel Cardell-Oliver                                      %
% DATE          : 1990                                                       %
%                                                                            %
%****************************************************************************%


let NOT_0_AND_MORE =prove_thm(`NOT_0_AND_MORE`,
 "!x:num. ~( (x=0) /\ (0<x) )",
  REPEAT STRIP_TAC THEN UNDISCH_TAC "0<x" THEN ASM_REWRITE_TAC[LESS_REFL]);;


close_theory ();;
