% FILE		: int_sbgp.show.ml					%
% DESCRIPTION   : This file gives a history of the development of some  %
%                 of the facts about subgroups of the integers which    %
%                 are relevant to the development of modular arithmetic.%
%                 It can be loaded by loadt and it will also create  	%
%                 int_sbgp.th, but in a most verbose manner.     	%
%									%
%									%
% AUTHOR	: E. L. Gunter						%
% DATE		: 89.4.11						%
%									%
%-----------------------------------------------------------------------%

new_theory `int_sbgp`;;

load_library `group`;;
load_library `integer`;;


set_goal ([],"!H.SUBGROUP((\N.T),$plus)H ==> NORMAL((\N.T),$plus)H");;

expand (GEN_TAC THEN DISCH_TAC THEN (ASM_REWRITE_TAC[NORMAL_DEF]));;

expand ((REPEAT STRIP_TAC) THEN (PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]));;

expand (NEW_SUBST1_TAC (SPECL ["n:integer";"x:integer"] COMM_PLUS));;

expand (PURE_ONCE_REWRITE_TAC[ASSOC_PLUS]);;

expand (ASM_REWRITE_TAC[PLUS_INV_LEMMA; PLUS_ID_LEMMA]);;


let INT_SBGP_NORMAL = prove_thm(`INT_SBGP_NORMAL`,
"!H. SUBGROUP((\N.T),$plus)H ==> NORMAL((\N.T),$plus)H",
(GEN_TAC THEN DISCH_TAC THEN (ASM_REWRITE_TAC[NORMAL_DEF]) THEN
 (REPEAT STRIP_TAC) THEN (PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]) THEN
 (NEW_SUBST1_TAC (SPECL ["n:integer";"x:integer"] COMM_PLUS)) THEN
 (PURE_ONCE_REWRITE_TAC[ASSOC_PLUS]) THEN
 (ASM_REWRITE_TAC[PLUS_INV_LEMMA; PLUS_ID_LEMMA])));;


set_goal ([],"!H.SUBGROUP((\N.T),$plus)H ==> H(INT 0)");;

expand (REPEAT STRIP_TAC);;

expand (PURE_ONCE_REWRITE_TAC [(SYM ID_EQ_0)]);;

expand (SUBST_MATCH_TAC (SYM (UNDISCH SBGP_ID_GP_ID)));;

expand GROUP_ELT_TAC;;

expand (POP_ASSUM \thm. (ACCEPT_TAC (CONJUNCT2 (CONJUNCT2
    (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF] thm)))));;


let INT_SBGP_ZERO = prove_thm (`INT_SBGP_ZERO`,
"!H.SUBGROUP((\N.T),$plus)H ==> H(INT 0)",
((REPEAT STRIP_TAC) THEN
 (PURE_ONCE_REWRITE_TAC [(SYM ID_EQ_0)]) THEN
 (SUBST_MATCH_TAC (SYM (UNDISCH SBGP_ID_GP_ID))) THEN
 GROUP_ELT_TAC THEN
 (POP_ASSUM \thm. (ACCEPT_TAC (CONJUNCT2 (CONJUNCT2
   (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF] thm)))))));;


set_goal ([],"!H.SUBGROUP((\N.T),$plus)H ==> !N. (H N ==> H (neg N))");;

expand (REPEAT STRIP_TAC);;

expand (STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF]
   (ASSUME "SUBGROUP((\N.T),$plus)H")));;

expand (PURE_ONCE_REWRITE_TAC [neg_DEF]);;

expand (SUBST_MATCH_TAC 
   (SYM (UNDISCH (SPEC_ALL (UNDISCH SBGP_INV_GP_INV)))));;

expand GROUP_ELT_TAC;;


let INT_SBGP_neg = prove_thm(`INT_SBGP_neg`,
"!H.SUBGROUP((\N.T),$plus)H ==> !N. (H N ==> H (neg N))",
((REPEAT STRIP_TAC) THEN
 (STRIP_ASSUME_TAC (PURE_ONCE_REWRITE_RULE [SUBGROUP_DEF]
    (ASSUME "SUBGROUP((\N.T),$plus)H"))) THEN
 (PURE_ONCE_REWRITE_TAC [neg_DEF]) THEN
 (SUBST_MATCH_TAC
    (SYM (UNDISCH (SPEC_ALL (UNDISCH SBGP_INV_GP_INV))))) THEN
 GROUP_ELT_TAC));;



let INT_MULT_SET_DEF = new_definition(`INT_MULT_SET_DEF`,
"int_mult_set n = \m. ?p. (m = p times n)");;


set_goal([],"!n.NORMAL((\N.T),$plus)(int_mult_set n)");;

expand (GEN_TAC THEN (MATCH_MP_IMP_TAC INT_SBGP_NORMAL));;

expand (REWRITE_TAC[SUBGROUP_LEMMA;INT_MULT_SET_DEF;integer_as_GROUP]);;

expand BETA_TAC;;

expand (REPEAT STRIP_TAC);;

% goal 1 -- int_mult_set is non-empty %

expand (EXISTS_TAC "INT 0");;

expand (EXISTS_TAC "INT 0");;

expand (REWRITE_TAC [TIMES_ZERO]);;

% goal 2 -- int_mult_set closed under addition %

expand (EXISTS_TAC "p plus p'");;

expand (ASM_REWRITE_TAC [RIGHT_PLUS_DISTRIB]);;

% goal 3 -- int_mult set closed under additive inverses %

expand (PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]);;

expand (EXISTS_TAC "neg p");;

expand (ASM_REWRITE_TAC[TIMES_neg]);;


let INT_MULT_SET_NORMAL = prove_thm(`INT_MULT_SET_NORMAL`,
"!n. NORMAL((\N. T),$plus)(int_mult_set n)",
(GEN_TAC THEN (MATCH_MP_IMP_TAC INT_SBGP_NORMAL) THEN
 (REWRITE_TAC[SUBGROUP_LEMMA;INT_MULT_SET_DEF;integer_as_GROUP]) THEN
 BETA_TAC THEN (REPEAT STRIP_TAC) THENL
 [((EXISTS_TAC "INT 0") THEN (EXISTS_TAC "INT 0") THEN
  (REWRITE_TAC [TIMES_ZERO]));
  ((EXISTS_TAC "p plus p'") THEN
   (ASM_REWRITE_TAC [RIGHT_PLUS_DISTRIB]));
  ((PURE_ONCE_REWRITE_TAC[(SYM neg_DEF)]) THEN
   (EXISTS_TAC "neg p") THEN
   (ASM_REWRITE_TAC[TIMES_neg]))]));;


close_theory ();;

