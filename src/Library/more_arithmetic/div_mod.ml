
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                            %
%   FILE:         div_mod.ml                                                 %
%   EDITOR:       Paul Curzon                                                %
%   DATE:         April 1993                                                 %
%   DESCRIPTION : Theorems about DIV and MOD		     		     %
%                                                                            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%*********************************  HISTORY  ********************************%
%									     %
%   This file is based on the theory of 				     %
%                                                                            %
%   Wai Wong                                                                 %
%                                                                            %
%****************************************************************************%

system `rm -f div_mod.th`;;

new_theory `div_mod`;;


%****************************************************************************%
%                                                                            %
% AUTHOR        : Wai Wong                                                   %
% DATE          : April 1993                                                 %
%                                                                            %
%****************************************************************************%

let SUC_MOD = prove_thm(`SUC_MOD`,
    "!n m. (SUC n) < m ==> ((SUC n) MOD m = SUC (n MOD m))",
    REPEAT STRIP_TAC THEN IMP_RES_TAC SUC_LESS
    THEN IMP_RES_TAC LESS_MOD THEN ASM_REWRITE_TAC[]);;

let NOT_MULT_LESS_0 = PROVE(
    "!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)",
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES;LESS_0]);;

let MOD_MULT_MOD = prove_thm(`MOD_MULT_MOD`,
    "!m n. (0 < n) /\ (0 < m)  ==> !x. ((x MOD (n * m)) MOD n = x  MOD n)",
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NOT_MULT_LESS_0)) THEN GEN_TAC
    THEN POP_ASSUM (CHOOSE_TAC o (MATCH_MP (SPECL ["x:num";"m * n"]DA)))
    THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
    THEN SUBST1_TAC (ASSUME"x = (q * (n * m)) + r")
    THEN POP_ASSUM (SUBST1_TAC o (SPEC "q:num") o (MATCH_MP MOD_MULT))
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN STRIP_ASSUME_TAC (ASSUME  "0 < n /\ 0 < m")
    THEN PURE_ONCE_REWRITE_TAC[UNDISCH_ALL(SPEC_ALL MOD_TIMES)]
    THEN REFL_TAC);;

let MULT_LEFT_1 = GEN_ALL (el 3 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));;
let MULT_RIGHT_1 = GEN_ALL (el 4 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));;

% MULT_DIV = |- !n q. 0 < n ==> ((q * n) DIV n = q) %
let MULT_DIV = save_thm(`MULT_DIV`,
    GEN_ALL (PURE_REWRITE_RULE[ADD_0]
    (CONV_RULE RIGHT_IMP_FORALL_CONV (SPECL["n:num";"0"] DIV_MULT))));;

% |- !q. q DIV (SUC 0) = q %
let DIV_ONE = save_thm(`DIV_ONE`,
    GEN_ALL (REWRITE_RULE[CONV_RULE (ONCE_DEPTH_CONV num_CONV) MULT_RIGHT_1]
    (MP (SPECL ["SUC 0"; "q:num"] MULT_DIV) (SPEC "0" LESS_0))));;

% LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) %
let LESS_DIV_EQ_ZERO = save_thm(`LESS_DIV_EQ_ZERO`,
    GEN_ALL (DISCH_ALL (PURE_REWRITE_RULE[MULT;ADD]
    (SPEC "0"(UNDISCH_ALL (SPEC_ALL  DIV_MULT))))));;

% SUC_MOD_SELF = |- !n. (SUC n) MOD (SUC n) = 0 %
let SUC_MOD_SELF = save_thm(`SUC_MOD_SELF`,
    GEN_ALL (REWRITE_RULE[MULT_CLAUSES]
    (SPEC "1"(MP (SPEC "SUC n" MOD_EQ_0) (SPEC "n:num" LESS_0)))));;

%  SUC_DIV_SELF = |- !n. (SUC n) DIV (SUC n) = 1 %
let SUC_DIV_SELF = save_thm(`SUC_DIV_SELF`,
    GEN_ALL (SYM (PURE_REWRITE_RULE[MULT_SUC_EQ]
    (TRANS (SPEC "SUC n" MULT_LEFT_1)
    (REWRITE_RULE[ADD_CLAUSES;SUC_MOD_SELF] (CONJUNCT1(SPEC "SUC n"
    (MP (SPEC "SUC n" DIVISION) (SPEC "n:num" LESS_0)))))))));;

let ADD_DIV_SUC_DIV = prove_thm(`ADD_DIV_SUC_DIV`,
    "!n. 0 < n ==> !r. (((n + r) DIV n) = SUC (r DIV n))",
    let MULT_LEM = SYM (PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(el 5 (CONJ_LIST 6 (SPECL["q:num";"n:num"] MULT_CLAUSES)))) in
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC "r < n" THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN SUBST_OCCS_TAC [[1],(SYM (SPEC"n:num" MULT_LEFT_1))]
      THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC "r:num" DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME "r = (q * n) + r'")
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN SUBST1_TAC MULT_LEM
      THEN IMP_RES_THEN (\t. REWRITE_TAC[t]) DIV_MULT]);;

let ADD_DIV_ADD_DIV = prove_thm(`ADD_DIV_ADD_DIV`,
    "!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))",
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC "r < n" THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC "r:num" DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME "r = (q * n) + r'")
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB]
      THEN IMP_RES_THEN (\t. REWRITE_TAC[t]) DIV_MULT]);;

let SUC_DIV_CASES = prove_thm(`SUC_DIV_CASES`,
    "!n. 0 < n ==> 
     !x. ((SUC x) DIV n  = x DIV n) \/ ((SUC x) DIV n = SUC(x DIV n))",
    let ADD_lemma = GEN_ALL (SYM (el 4 (CONJ_LIST 4 ADD_CLAUSES))) in
    REPEAT STRIP_TAC THEN IMP_RES_THEN 
      (\t. (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC "x:num" t))) DA
    THEN PURE_ONCE_REWRITE_TAC[ADD_lemma]
    THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) ADD_DIV_ADD_DIV
    THEN DISJ_CASES_THEN2 ASSUME_TAC (\t.SUBST_OCCS_TAC[[3],SYM t])
      (PURE_ONCE_REWRITE_RULE[LESS_OR_EQ](MATCH_MP LESS_OR (ASSUME " r < n")))
    THENL[
      DISJ1_TAC THEN IMP_RES_TAC LESS_DIV_EQ_ZERO
      THEN ASM_REWRITE_TAC[ADD_0];
      DISJ2_TAC THEN PURE_ONCE_REWRITE_TAC[SUC_DIV_SELF]
      THEN IMP_RES_TAC LESS_DIV_EQ_ZERO
      THEN ASM_REWRITE_TAC[ADD_CLAUSES;(GSYM ADD1)]]);;

let Less_lemma = PROVE(
    "!m n. m < n ==> ?p. (n = m + p) /\ 0 < p",
    GEN_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0];
      REWRITE_TAC[LESS_THM]
      THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
    	EXISTS_TAC "1" THEN CONV_TAC ((RAND_CONV o RAND_CONV)num_CONV)
    	THEN REWRITE_TAC[LESS_0;ADD1];
    	RES_TAC THEN EXISTS_TAC "SUC p"
    	THEN ASM_REWRITE_TAC[ADD_CLAUSES;LESS_0]]]);;

let LESS_MONO_DIV = PROVE(
    "!n. 0 < n ==> !p q. p < q ==> ((p DIV n) <= (q DIV n))",
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN DISCH_THEN ((CHOOSE_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) o
    	(MATCH_MP Less_lemma))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC "p:num" (MATCH_MP DA (ASSUME "0 < n")))
    THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN IMP_RES_TAC ADD_DIV_ADD_DIV
    THEN ASM_REWRITE_TAC[LESS_EQ_ADD]);;

let LESS_EQ_MONO_DIV = prove_thm(`LESS_EQ_MONO_DIV`,
    "!n. 0 < n ==> !p q. p <= q ==> ((p DIV n) <= (q DIV n))",
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN DISCH_THEN (\t. DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC
    	(REWRITE_RULE[LESS_OR_EQ]t)) THENL[
     IMP_RES_TAC LESS_MONO_DIV;
     REWRITE_TAC[LESS_EQ_REFL]]);;

let Less_MULT_lemma = PROVE(
    "!r m p. 0 < p ==> (r < m) ==> (r < (p * m))",
    let lem1 = MATCH_MP LESS_LESS_EQ_TRANS 
    	(CONJ (SPEC "m:num" LESS_SUC_REFL)
    	      (SPECL["SUC m"; "p*(SUC m)"] LESS_EQ_ADD)) in
    GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN DISCH_TAC THEN REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
    THEN PURE_ONCE_REWRITE_TAC[MULT]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THENL[
      ACCEPT_TAC lem1;
      ACCEPT_TAC (MATCH_MP LESS_TRANS (CONJ (ASSUME "r < m") lem1))]);;

let Less_MULT_ADD_lemma = PROVE(
  "!m n r r'. 0 < m /\ 0 < n /\ r < m /\ r' < n ==> ((r' * m) + r) < (n * m)",
    REPEAT STRIP_TAC
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME "r < m"))
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME "r' < n"))
    THEN ASM_REWRITE_TAC[]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_ADD_EQ]
    THEN SUBST1_TAC (SYM (ASSUME"m = r + p"))
    THEN IMP_RES_TAC Less_MULT_lemma);;

let DIV_DIV_DIV_MULT = prove_thm(`DIV_DIV_DIV_MULT`,
    "!m n. (0 < m) /\ (0 < n)  ==> !x. ((x DIV m) DIV n = x  DIV (m * n))",
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC "x:num" (MATCH_MP DA (ASSUME "0 < m")))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC "q:num" (MATCH_MP DA (ASSUME "0 < n")))
    THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) DIV_MULT
    THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN ASSUME_TAC (MATCH_MP NOT_MULT_LESS_0
    	(CONJ (ASSUME "0 < n") (ASSUME "0 < m")))
    THEN CONV_TAC ((RAND_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN FIRST_ASSUM (\t.REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV t])
    THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO
    THEN IMP_RES_TAC Less_MULT_ADD_lemma);;

close_theory();;
