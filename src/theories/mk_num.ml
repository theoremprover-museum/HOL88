%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_num.ml                                             %
%                                                                             %
%     DESCRIPTION:      Creates the theory "num.th" containing Peano's        %
%                       postulates for the natural numbers.                   %
%                                                                             %
%     AUTHOR:           T. F. Melham (88.04.02)                               %
%                                                                             %
%     PARENTS:          BASIC-HOL.th                                          %
%     WRITES FILES:     num.th                                                %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        University of Edinburgh                               %
%     COPYRIGHT:        University of Cambridge                               %
%     COPYRIGHT:        INRIA                                                 %
%                                                                             %
%     REVISION HISTORY: (none)                                                %
%=============================================================================%

% Create the theory							%
new_theory `num`;;

let INFINITY_AX = axiom `ind` `INFINITY_AX`;;

let ONE_ONE_DEF = definition `bool` `ONE_ONE_DEF`;;
let ONTO_DEF = definition `bool` `ONTO_DEF`;;

% Define successor "SUC_REP:ind->ind" on ind.				%
let SUC_REP_DEF = 
    new_definition
    (`SUC_REP_DEF`, 
     "SUC_REP = @f:ind->ind. ONE_ONE f /\ ~(ONTO f)");;
     
% "ZERO_REP:ind" represents "0:num" 					%
let ZERO_REP_DEF = 
    new_definition
    (`ZERO_REP_DEF`, "ZERO_REP = @x:ind. !y. ~(x = SUC_REP y)");;


% "IS_NUM:ind->bool" defines the subset of ":ind" used to represent 	%
% numbers.  It is the smallest subset containing "ZERO_REP" and closed	%
% under "SUC_REP" 							%
let IS_NUM_REP = 
    new_definition
    (`IS_NUM_REP`,
     "IS_NUM_REP m = 
      !P:ind->bool. P ZERO_REP /\ (!n. P n ==> P(SUC_REP n)) ==> P m");;

% Prove that there is a representation in ind of at least one number.	%
let EXISTS_NUM_REP = 
    TAC_PROOF
    (([],"?n. IS_NUM_REP n"),
     PURE_REWRITE_TAC [IS_NUM_REP] THEN
     EXISTS_TAC "ZERO_REP" THEN
     REPEAT STRIP_TAC);;

% make the type definition.						%
let num_TY_DEF = 
    new_type_definition (`num`, "IS_NUM_REP", EXISTS_NUM_REP);;

% --------------------------------------------------------------------- %
% Define a representation function, REP_num, from the type num to 	%
% the representing type ind, and the inverse abstraction 		%
% function ABS_num, and prove some trivial lemmas about them.		%
% --------------------------------------------------------------------- %

let num_ISO_DEF = 
    define_new_type_bijections
        `num_ISO_DEF` `ABS_num` `REP_num` num_TY_DEF;;

let R_11   = prove_rep_fn_one_one num_ISO_DEF  and
    R_ONTO = prove_rep_fn_onto num_ISO_DEF     and
    A_11   = prove_abs_fn_one_one num_ISO_DEF  and
    A_ONTO = prove_abs_fn_onto num_ISO_DEF;;

% The following hack, and explanation are mjcg's			%
%									%
% "0" is defined to be the element of ":num" that 			%
% is represented by "ZERO_REP". Unfortunately we cannot use the ML	%
% function new_definition as "0" is recognised by the parser as		%
% a constant of type ":num" (a hack needed to get over the problem that	%
% there are infinitely many numerals) and so new_definition thinks	%
% one is trying to redefine a constant. The following lisp hack fixes	%
% things by switching off the automatic constantization of numerals. 	%

% MJCG 9/11/88 for HOL88                                                %
% Redefined numconstp rather than constp                                %

lisp `(setdebug t)`;;
lisp `(defun numconstp (tok) nil)`;;

let ZERO_DEF = 
    new_definition(`ZERO_DEF`, "0 = ABS_num(ZERO_REP)");;

% Define the successor function on num.					%
let SUC_DEF = 
    new_definition(`SUC_DEF`, "SUC m = ABS_num(SUC_REP(REP_num m))");;

close_theory();;

% Prove that IS_NUM_REP ZERO_REP					%
let IS_NUM_REP_ZERO = 
    TAC_PROOF
    (([], "IS_NUM_REP ZERO_REP"),
     REWRITE_TAC [IS_NUM_REP] THEN REPEAT STRIP_TAC);;

% Prove that IS_NUM_REP (SUC_REP x)					%
let IS_NUM_SUC_REP = 
    TAC_PROOF
    (([], "!i. IS_NUM_REP i ==> IS_NUM_REP (SUC_REP i)"),
     REWRITE_TAC [IS_NUM_REP] THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);;

let IS_NUM_REP_SUC_REP = 
    TAC_PROOF
    (([], "!n. IS_NUM_REP(SUC_REP(REP_num n))"),
      GEN_TAC THEN MATCH_MP_TAC IS_NUM_SUC_REP THEN
      REWRITE_TAC [R_ONTO] THEN 
      EXISTS_TAC "n:num" THEN REFL_TAC);;

% Prove that SUC_REP is one-to-one and ZERO_REP ~= SUC_REP i.		%

let thm1 = REWRITE_RULE [SYM SUC_REP_DEF] (SELECT_RULE INFINITY_AX);;
let thm2 = REWRITE_RULE [ONE_ONE_DEF;ONTO_DEF] thm1;;


% |- !x1 x2. (SUC_REP x1 = SUC_REP x2) ==> (x1 = x2)			%
let SUC_REP_11 = CONJUNCT1 thm2;;

%  |- !x. ~(SUC_REP x = ZERO_REP)					%
let NOT_SUC_ZERO = 
    let th1 = CONV_RULE NOT_FORALL_CONV (CONJUNCT2 thm2) in
    let th2 = CONV_RULE (ONCE_DEPTH_CONV NOT_EXISTS_CONV) th1 in
    let th3 = SELECT_RULE th2 in
    let th4 = REWRITE_RULE [SYM ZERO_REP_DEF] th3 in
        CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) th4;;


% ---------------------------------------------------------------------	%
% Proof of NOT_SUC : |- !n. ~(SUC n = 0)				%
% ---------------------------------------------------------------------	%


let NOT_SUC = 
    prove_thm
    (`NOT_SUC`,
     "!n. ~(SUC n = 0)",
     PURE_REWRITE_TAC [SUC_DEF;ZERO_DEF] THEN GEN_TAC THEN
     MP_TAC (SPECL ["SUC_REP(REP_num n)";"ZERO_REP"] A_11) THEN
     REWRITE_TAC [IS_NUM_REP_ZERO;IS_NUM_REP_SUC_REP] THEN
     DISCH_THEN SUBST1_TAC THEN
     MATCH_ACCEPT_TAC NOT_SUC_ZERO);;

% ---------------------------------------------------------------------	%
% Prove that |-  !m n. (SUC m = SUC n) ==> (m = n)			%
% ---------------------------------------------------------------------	%
     
let INV_SUC = 
    prove_thm
    (`INV_SUC`,
     "!m n. (SUC m = SUC n) ==> (m = n)",
     REPEAT GEN_TAC THEN REWRITE_TAC [SUC_DEF] THEN
     MP_TAC (SPECL ["SUC_REP(REP_num m)";"SUC_REP(REP_num n)"] A_11) THEN
     REWRITE_TAC [IS_NUM_REP_SUC_REP] THEN DISCH_THEN SUBST1_TAC THEN
     DISCH_THEN (MP_TAC o MATCH_MP SUC_REP_11) THEN
     REWRITE_TAC [R_11]);;

% ---------------------------------------------------------------------	%
% Prove induction theorem.						%
% ---------------------------------------------------------------------	%

let ind_lemma1 = 
    TAC_PROOF
    (([], "!P. P ZERO_REP /\ (!i. (P i ==> P(SUC_REP i))) ==>
	      (!i. IS_NUM_REP i ==> P i)"),
     PURE_ONCE_REWRITE_TAC [IS_NUM_REP] THEN
     REPEAT STRIP_TAC THEN RES_TAC);;

let lemma = 
    TAC_PROOF(([], "(A ==> A /\ B) = (A ==> B)"),
               ASM_CASES_TAC "A:bool" THEN ASM_REWRITE_TAC []);;

let ind_lemma2 = 
    TAC_PROOF
    (([], "!P. P ZERO_REP /\ (!i. (IS_NUM_REP i /\ P i ==> P(SUC_REP i))) ==>
	      (!i. IS_NUM_REP i ==> P i)"),
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC (SPEC "\i. IS_NUM_REP i /\ P i" ind_lemma1) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [lemma] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [IS_NUM_REP_ZERO] THEN 
     REPEAT STRIP_TAC THEN IMP_RES_TAC IS_NUM_SUC_REP THEN
     RES_TAC);;

let lemma1 = 
    TAC_PROOF
    (([], "(!i. IS_NUM_REP i ==> P(ABS_num i)) = (!n. P n)"),
     EQ_TAC THEN REPEAT STRIP_TAC THENL
     [STRIP_ASSUME_TAC (SPEC "n:num" A_ONTO) THEN 
      RES_TAC THEN ASM_REWRITE_TAC [];
      POP_ASSUM MP_TAC THEN REWRITE_TAC [R_ONTO] THEN
      STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC []]);;

let INDUCTION = 
    prove_thm
    (`INDUCTION`,
     "!P. (P 0 /\ (!n. P n ==> P(SUC n))) ==> !n. P n",
     GEN_TAC THEN STRIP_TAC THEN 
     MP_TAC (SPEC "\i. P(ABS_num i):bool" ind_lemma2) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [SYM ZERO_DEF;lemma1] THEN
     DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC [R_ONTO] THEN 
      GEN_TAC THEN  CONV_TAC ANTE_CONJ_CONV THEN
      DISCH_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC [num_ISO_DEF;SYM (SPEC_ALL SUC_DEF)]]);;

quit();;
