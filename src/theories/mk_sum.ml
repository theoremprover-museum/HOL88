%=============================================================================%
%                               HOL 88 Version 2.0                            %
%                                                                             %
%     FILE NAME:        mk_sum.ml                                             %
%                                                                             %
%     DESCRIPTION:      Creates the theory "sum.th" containing the logical    %
%                       definition of the sum type operator.  The sum type is %
%                       defined and the following "axiomatization" is proven  %
%                       from the definition of the type:                      %
%                                                                             %
%                       |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)          %
%                                                                             %
%                       Using this axiom, the following standard theorems are %
%                       proved.                                               %
%                                                                             %
%                       |- ISL (INL a)                |- ISR (INR b)          %
%                       |- ~ISL (INR b)               |- ~ISR (INL a)         %
%                       |- OUTL (INL a) = a           |- OUTR (INR b) = b     %
%                       |- ISL(x) ==> INL (OUTL x)=x                          %
%                       |- ISR(x) ==> INR (OUTR x)=x                          %
%                       |- !x. ISL x \/ ISR x                                 %
%                                                                             %
%     AUTHOR:           T. F. Melham (86.11.24)                               %
%                                                                             %
%     PARENTS:          combin.th                                             %
%     WRITES FILES:     sum.th                                                %
%                                                                             %
%                       University of Cambridge                               %
%                       Hardware Verification Group                           %
%                       Computer Laboratory                                   %
%                       New Museums Site                                      %
%                       Pembroke Street                                       %
%                       Cambridge  CB2 3QG                                    %
%                       England                                               %
%                                                                             %
%     COPYRIGHT:        T. F. Melham 1987                                     %
%                                                                             %
%     REVISION HISTORY: 87.03.14 90.04.10 90.09.09                            %
%=============================================================================%

% --------------------------------------------------------------------- %
% Create and open the new theory sum.th.				%
% --------------------------------------------------------------------- %
new_theory `sum`;;

% parent theory is theory of combinators.				%
new_parent `combin`;;

% Fetch theorems needed from combin.th					%
let o_DEF = definition `combin` `o_DEF`;;
let o_THM = theorem `combin` `o_THM`;;

% ===================================================================== %
% Introduce the new type.						%
% ===================================================================== %

% --------------------------------------------------------------------- %
% The sum of types ":*" and ":**" will be represented by a certain	%
% subset of type ":bool->*->**->bool".  A left injection of value "p:*" %
% will be represented by:  "\b x y. x=p /\ b". A right injection of	%
% value "q:**" will be represented by:  "\b x y. x=q /\ ~b".		%
% The predicate IS_SUM_REP is true of just those objects of the type	%
% ":bool->*->**->bool" which are representations of some injection.	%
% --------------------------------------------------------------------- %

let IS_SUM_REP = 
    new_definition
     (`IS_SUM_REP`,
      "IS_SUM_REP (f:bool->*->**->bool) = 
       ?v1 v2.  (f = \b x y.(x=v1) /\ b) \/ (f = \b x y.(y=v2) /\ ~b)");;

% --------------------------------------------------------------------- %
% Prove that there exists some object in the representing type that 	%
% lies in the subset of legal representations.				%
% --------------------------------------------------------------------- %

let EXISTS_SUM_REP = 
    TAC_PROOF(([], "?f:bool -> * -> ** -> bool. IS_SUM_REP f"),
	      EXISTS_TAC "\b x (y:**). (x=@x:*.T) /\ b" THEN
	      PURE_ONCE_REWRITE_TAC [IS_SUM_REP] THEN
	      EXISTS_TAC "@x:*.T" THEN REWRITE_TAC []);;

% --------------------------------------------------------------------- %
% Use the type definition mechanism to introduce the new type.		%
% The theorem returned is:  |- ?rep. TYPE_DEFINITION IS_SUM_REP rep 	%
% --------------------------------------------------------------------- %

let sum_TY_DEF = 
  new_type_definition 
  (`sum`, "IS_SUM_REP:(bool -> * -> ** -> bool) -> bool", EXISTS_SUM_REP);;

% --------------------------------------------------------------------- %
% Define a representation function, REP_sum, from the type (*,**)sum to %
% the representing type bool->*->**->bool, and the inverse abstraction 	%
% function ABS_sum, and prove some trivial lemmas about them.		%
% --------------------------------------------------------------------- %

let sum_ISO_DEF = 
    define_new_type_bijections
        `sum_ISO_DEF` `ABS_sum` `REP_sum` sum_TY_DEF;;


let R_A    = GEN_ALL (SYM (SPEC_ALL (CONJUNCT2 sum_ISO_DEF))) and
    R_11   = SYM(SPEC_ALL (prove_rep_fn_one_one sum_ISO_DEF)) and
    A_ONTO = REWRITE_RULE [IS_SUM_REP] 
    			  (prove_abs_fn_onto sum_ISO_DEF);;

% --------------------------------------------------------------------- %
% The definitions of the constants INL and INR follow:			%
% --------------------------------------------------------------------- %

% Define the injection function INL:*->(*,**)sum			%
let INL_DEF = 
    new_definition
	(`INL_DEF`,
         "!e.(INL:*->(*,**)sum) e = ABS_sum(\b x (y:**). (x = e) /\ b)");;

% Define the injection function INR:**->(*,**)sum			%
let INR_DEF = 
    new_definition
	(`INR_DEF`,
         "!e.(INR:**->(*,**)sum) e = ABS_sum(\b (x:*) y. (y = e) /\ ~b)");;

% ===================================================================== %
% The proof of the "axiom" for sum types follows.			%
% ===================================================================== %

% Two abbreviations.  NB: local to this file only! [TFM 90.05.26]	%
let SIMP = REWRITE_RULE [];;
let REWRITE1_TAC th = REWRITE_TAC [th];;

% Prove that REP_sum(INL v) gives the representation of INL v.		%
let REP_INL = 
    TAC_PROOF(([], "REP_sum (INL v) = \b x (y:**). (x:* = v) /\ b"),
	      PURE_REWRITE_TAC [INL_DEF;R_A;IS_SUM_REP] THEN
	      EXISTS_TAC "v:*" THEN
	      REWRITE_TAC[]);;

% Prove that REP_sum(INR v) gives the representation of INR v.		%
let REP_INR = 
    TAC_PROOF(([], "REP_sum (INR v) = \b (x:*) y. (y:** = v) /\ ~b"),
	      PURE_REWRITE_TAC [INR_DEF;R_A;IS_SUM_REP] THEN
	      MAP_EVERY EXISTS_TAC ["v:*";"v:**"] THEN
	      REWRITE_TAC[]);;

% Prove that INL is one-to-one						%
let INL_11 = 
    TAC_PROOF(([], "(INL x = (INL y:(*,**)sum)) = (x = y)"),
      EQ_TAC THENL
      [PURE_REWRITE_TAC [R_11;REP_INL] THEN
       CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
       DISCH_THEN (ACCEPT_TAC o SIMP o SPECL ["T";"x:*";"y:**"]);
       DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

% Prove that INR is one-to-one						%
let INR_11 = 
    TAC_PROOF(([], "(INR x = (INR y:(*,**)sum)) = (x = y)"),
      EQ_TAC THENL
      [PURE_REWRITE_TAC [R_11;REP_INR] THEN
       CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
       DISCH_THEN (ACCEPT_TAC o SYM o SIMP o SPECL["F";"x:*";"y:**"]);
       DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

% Prove that left injections and right injections are not equal.	%
let INR_neq_INL = 
    TAC_PROOF(([],"!v1 v2. ~(INR v2:(*,**)sum = INL v1)"),
      PURE_REWRITE_TAC [R_11;REP_INL;REP_INR] THEN
      REPEAT GEN_TAC THEN
      CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
      DISCH_THEN (CONTR_TAC o SIMP o SPECL ["T";"v1:*";"v2:**"]));;

% Prove a little lemma about epsilon-terms.				%
let EPS_lemma = 
    TAC_PROOF(([], "(@x:*.y=x) = y"),
      CONV_TAC (SYM_CONV THENC SELECT_CONV) THEN 
      EXISTS_TAC "y:*" THEN REFL_TAC);;

% --------------------------------------------------------------------- %
% The abstract "axiomatization" of the sum type consists of the single	%
% theorem given below:							%
%									%
% sum_axiom    |- !f g. ?!h. (h o INL = f) /\ (h o INR = g)		%
%									%
% The definitions of the usual operators ISL, OUTL, etc. follow from 	%
% this axiom.								%
% --------------------------------------------------------------------- %

let sum_axiom = 
    prove_thm(`sum_axiom`,
	      "!f:*->***. !g:**->***. ?!h. (h o INL = f) /\ (h o INR = g)",
	      PURE_REWRITE_TAC [EXISTS_UNIQUE_DEF;o_DEF] THEN
	      CONV_TAC (REDEPTH_CONV (BETA_CONV ORELSEC FUN_EQ_CONV)) THEN
	      REPEAT (FILTER_STRIP_TAC "x:(*,**)sum->***") THENL
	      [EXISTS_TAC "\x:(*,**)sum.((?v1. x = INL v1) => 
				           f(@v1.x = INL v1) | 
					   g(@v2.x = INR v2)):***" THEN
	       PURE_REWRITE_TAC [EXISTS_DEF] THEN
 	       CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
	       REWRITE_TAC [INL_11;INR_11;INR_neq_INL;EPS_lemma];
	       REPEAT GEN_TAC THEN
	       DISCH_THEN (CONJUNCTS_THEN2 MP_TAC 
	        (REWRITE1_TAC o (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)))) THEN
	       REPEAT STRIP_TAC THEN
	       STRIP_ASSUME_TAC (SPEC "s:(*,**)sum" A_ONTO) THEN
	       ASM_REWRITE_TAC (map (SYM o SPEC_ALL) [INL_DEF;INR_DEF])]);; 

% --------------------------------------------------------------------- %
% We also prove a version of sum_axiom which is in a form suitable for  %
% use with the recursive type definition tools.				%
% --------------------------------------------------------------------- %

let sum_Axiom = 
    prove_thm
     (`sum_Axiom`, 
      "!f:*->***. !g:**->***. ?! h. 
         (!x. h(INL x) = f x) /\ (!y. h(INR y) = g y)",
    let cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom in
    let rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv) in
    MATCH_ACCEPT_TAC rew);;


% ---------------------------------------------------------------------	%
% The definitions of ISL, ISR, OUTL, OUTR follow.			%
% --------------------------------------------------------------------- %


% Derive the defining property for ISL.					%
let ISL_DEF = 
    TAC_PROOF(([], "?ISL. (!x:*. ISL(INL x)) /\ (!y:**. ~ISL(INR y))"),
     let inst = (INST_TYPE [":bool",":***"] sum_axiom) in
     let spec = SPECL ["\x:*.T"; "\y:**.F"] inst in
     let exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec) in
     let conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth in
     STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
     EXISTS_TAC "h:(*,**)sum->bool" THEN ASM_REWRITE_TAC []);;

% Then define ISL with a constant specification.			%
let ISL = new_specification `ISL` [`constant`,`ISL`] ISL_DEF;;

% Derive the defining property for ISR.					%
let ISR_DEF = 
    TAC_PROOF(([], "?ISR. (!x:**. ISR(INR x)) /\ (!y:*. ~ISR(INL y))"),
     let inst = (INST_TYPE [":bool",":***"] sum_axiom) in
     let spec = SPECL ["\x:*.F"; "\y:**.T"] inst in
     let exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec) in
     let conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth in
     STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] conv) THEN
     EXISTS_TAC "h:(*,**)sum->bool" THEN ASM_REWRITE_TAC []);;

% Then define ISR with a constant specification.			%
let ISR = new_specification `ISR` [`constant`,`ISR`] ISR_DEF;;

% Derive the defining property of OUTL.					%
let OUTL_DEF = 
    TAC_PROOF(([], "?OUTL. !x. OUTL(INL x:(*,**)sum) = x"),
     let inst = (INST_TYPE [":*",":***"] sum_axiom) in
     let spec = SPECL ["\x:*.x"; "\y:**.@x:*.F"] inst in
     let exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec) in
     let conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth in
     STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
     EXISTS_TAC "h:(*,**)sum->*" THEN ASM_REWRITE_TAC []);;	

% Then define OUTL with a constant specification.			%
let OUTL = new_specification `OUTL` [`constant`,`OUTL`] OUTL_DEF;;

% Derive the defining property of OUTR.					%
let OUTR_DEF = 
    TAC_PROOF(([], "?OUTR. !x. OUTR(INR x:(*,**)sum) = x"),
     let inst = (INST_TYPE [":**",":***"] sum_axiom) in
     let spec = SPECL ["\x:*.@y:**.F"; "\y:**.y"] inst in
     let exth = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV spec) in
     let conv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) exth in
     STRIP_ASSUME_TAC (REWRITE_RULE [o_THM] (BETA_RULE conv)) THEN
     EXISTS_TAC "h:(*,**)sum->**" THEN ASM_REWRITE_TAC []);;	

% Then define OUTR with a constant specification.			%
let OUTR = new_specification `OUTR` [`constant`,`OUTR`] OUTR_DEF;;

% Close the theory.                                                     %
close_theory();;


% ---------------------------------------------------------------------	%
% Prove the following standard theorems about the sum type.		%
%									%
%	  	  |- ISL(s) ==> INL (OUTL s)=s				%
%		  |- ISR(s) ==> INR (OUTR s)=s				%
%	  	  |- !s. ISL s \/ ISR s					%
%		  							%
% ---------------------------------------------------------------------	%

% First, get the existence and uniqueness parts of sum_axiom.		%
%									%
% sum_EXISTS: 								%
%   |- !f g. ?h. (!x. h(INL x) = f x) /\ (!x. h(INR x) = g x) 		%
%									%
% sum_UNIQUE: 								%
%   |- !f g x y.							%
%       ((!x. x(INL x) = f x) /\ (!x. x(INR x) = g x)) /\		%
%       ((!x. y(INL x) = f x) /\ (!x. y(INR x) = g x)) ==>		%
%       (!s. x s = y s)							%

let [sum_EXISTS;sum_UNIQUE] = 
    let cnv = CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) sum_axiom in
    let rew = SPEC_ALL (REWRITE_RULE [o_THM] cnv) in
    let [a;b] = map GEN_ALL (CONJUNCTS (CONV_RULE EXISTS_UNIQUE_CONV rew)) in
    [a; BETA_RULE (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) b)];;

% Prove the following key lemma by contradiction.			%

let sum_lemma = 
    let lemma = 
        TAC_PROOF (([],"~~!v:(*,**)sum. (?x. v = INL x) \/ (?x. v = INR x)"),
        CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
        PURE_REWRITE_TAC [DE_MORGAN_THM] THEN
        DISCH_THEN (STRIP_ASSUME_TAC o 
	           (CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV))) THEN
        MP_TAC (SPECL ["\x:*.T";"\x:**.F";
	               "\v':(*,**)sum. ((v = v') => T | ISL v')";
		       "ISL:(*,**)sum->bool"] 
		       (INST_TYPE [":bool",":***"] sum_UNIQUE)) THEN
        MP_TAC (SPECL ["\x:*.T";"\x:**.F";
		       "\v':(*,**)sum. ((v = v') => F | ISL v')";
		       "ISL:(*,**)sum->bool"] 
		       (INST_TYPE [":bool",":***"] sum_UNIQUE)) THEN
        CONV_TAC (DEPTH_CONV BETA_CONV) THEN
        ASM_REWRITE_TAC [ISR;ISL] THEN
        DISCH_THEN (\th. PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL th)]) THEN
        DISCH_THEN (MP_TAC o SPEC "v:(*,**)sum") THEN
        REWRITE_TAC[]) in
    REWRITE_RULE [] lemma;;

% Prove that: !x. ISL(x) \/ ISR(x)					%
let ISL_OR_ISR = 
    prove_thm
    (`ISL_OR_ISR`, "!x:(*,**)sum. ISL(x) \/ ISR(x)",
     STRIP_TAC THEN
     STRIP_ASSUME_TAC (SPEC "x:(*,**)sum" sum_lemma) THEN
     ASM_REWRITE_TAC [ISL;ISR]);;

% Prove that: |- !x. ISL(x) ==> INL (OUTL x) = x			%
let INL = 
    prove_thm(`INL`,
	      "!x:(*,**)sum. ISL(x) ==> (INL (OUTL x) = x)",
	      STRIP_TAC THEN
              STRIP_ASSUME_TAC (SPEC "x:(*,**)sum" sum_lemma) THEN
	      ASM_REWRITE_TAC [ISL;OUTL]);;

% Prove that: |- !x. ISR(x) ==> INR (OUTR x) = x			%
let INR = 
    prove_thm(`INR`,
	      "!x:(*,**)sum. ISR(x) ==> (INR (OUTR x) = x)",
	      STRIP_TAC THEN
              STRIP_ASSUME_TAC (SPEC "x:(*,**)sum" sum_lemma) THEN
	      ASM_REWRITE_TAC [ISR;OUTR]);;

quit();;
