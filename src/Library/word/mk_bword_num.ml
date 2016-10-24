% ===================================================== %
% FILE: mk_bword_num.ml	    DATE: 14 Aug 1992		%
% AUTHOR: Wai WONG  	    	    			%
% Writes: bword_base.th	    	    			%
% Uses: Libraries: arith res_quan			%
% Description: Creates a theorey for mapping between 	%
% natural numbers and boolean words	    	    	%
% ===================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

loadt(`ver_`^(string_of_int(version())));;

loadf`arith_thms`;;

load_theory `word_bitop`;;

new_theory`bword_num`;;

new_parent  `word_num`;;

map autoload_all [`word_base`; `word_bitop`; `word_num`];;

loadf`word_funs`;;

%---------------------------------------------------------------%
% Mapping between (bool)word and num 				%
%---------------------------------------------------------------%

let BV_DEF = new_definition(`BV_DEF`,
    "BV b = (b => SUC 0 | 0)");;

% BNVAL w converts the boolean word w to a num %
let BNVAL_DEF = new_recursive_definition false word_Ax `BNVAL_DEF`
    "BNVAL (WORD l) = LVAL BV 2 l";;

let BV_LESS_2 = prove_thm(`BV_LESS_2`, "!x. BV x < 2",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN COND_CASES_TAC THEN CONV_TAC (REDEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LESS_0;LESS_MONO_EQ]);;

let BNVAL_NVAL = prove_thm(`BNVAL_NVAL`,
    "!w. BNVAL w = NVAL BV 2 w",
    let lem1 = REWRITE_RULE[GSYM NVAL_DEF] BNVAL_DEF in
    word_INDUCT_TAC THEN MATCH_ACCEPT_TAC lem1);;

let BNVAL0 = save_thm(`BNVAL0`,    % BNVAL (WORD[]) = 0 %
    TRANS (SPEC "WORD[]:bool word" BNVAL_NVAL) (ISPECL ["BV"; "2"] NVAL0));;

let BNVAL_11_lem = PROVE("!m n p. m < p /\ n < p ==> ~((p + m) =  n)",
    INDUCT_TAC THENL[
      REPEAT GEN_TAC THEN STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN CONV_TAC (RAND_CONV SYM_CONV) THEN IMP_RES_TAC LESS_NOT_EQ;
      INDUCT_TAC THEN GEN_TAC THEN STRIP_TAC THENL[
    	PURE_ONCE_REWRITE_TAC[ADD_EQ_0]
    	THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM]
    	THEN DISJ2_TAC THEN MATCH_ACCEPT_TAC NOT_SUC;
    	PURE_REWRITE_TAC[ADD_CLAUSES;INV_SUC_EQ]
    	THEN IMP_RES_TAC SUC_LESS THEN RES_TAC]]);;

let BNVAL_11 = prove_thm(`BNVAL_11`,
    "!w1 w2:(bool)word. (WORDLEN w1 = WORDLEN w2) ==>
     (BNVAL w1 = BNVAL w2) ==> (w1 = w2)",
    let lem1 = BNVAL_11_lem in
    let lem2 = GEN_ALL(MATCH_MP LVAL_MAX BV_LESS_2) in
    word_INDUCT_TAC THEN GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WORDLEN_DEF;WORD_11;BNVAL_DEF]
    THEN SPEC_TAC ("l:(bool)list","l:(bool)list")
    THEN EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[LVAL;BV_DEF;CONS_11]
    THEN FIRST_ASSUM SUBST1_TAC THEN REPEAT COND_CASES_TAC THENL[
      PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[EQ_MONO_ADD_EQ]
      THEN DISCH_TAC THEN RES_TAC;
      PURE_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES]
      THEN ASSUME_TAC (ISPEC "l':bool list" lem2)
      THEN ASSUME_TAC(SUBS[ASSUME"LENGTH(l:bool list) = LENGTH(l':bool list)"]
    	(ISPEC "l:bool list" lem2))
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[];
      PURE_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES]
      THEN ASSUME_TAC (ISPEC "l':bool list" lem2)
      THEN ASSUME_TAC(SUBS[ASSUME"LENGTH(l:bool list) = LENGTH(l':bool list)"]
    	(ISPEC "l:bool list" lem2))
      THEN CONV_TAC ((RATOR_CONV o RAND_CONV) SYM_CONV)
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[];
      PURE_REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES]
      THEN RES_TAC THEN ASM_REWRITE_TAC[]]);;

let BNVAL_ONTO = prove_thm(`BNVAL_ONTO`,
    "!w. ?n. BNVAL w = n",
    word_INDUCT_TAC THEN REWRITE_TAC[BNVAL_DEF]
    THEN LIST_INDUCT_TAC THENL[
      EXISTS_TAC "0";
      GEN_TAC THEN EXISTS_TAC
       "((BV h) * (2 EXP (LENGTH (l:bool list)))) + (LVAL BV 2 l)"]
    THEN REWRITE_TAC[LVAL]);;

let BNVAL_MAX = prove_thm(`BNVAL_MAX`,
    "!n. !w:(bool)word ::PWORDLEN n. BNVAL w < (2 EXP n)",
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[BNVAL_DEF]
    THEN FIRST_ASSUM SUBST1_TAC THEN MATCH_MP_TAC LVAL_MAX
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN COND_CASES_TAC THEN CONV_TAC (REDEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LESS_0;LESS_MONO_EQ]);;

let BNVAL_WCAT1 = prove_thm(`BNVAL_WCAT1`,
    "!n. !w:(bool)word::PWORDLEN n.
     !x:bool. BNVAL (WCAT (w,WORD[x])) = ((BNVAL w) * 2)  + (BV x)",
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN GEN_TAC
    THEN REWRITE_TAC[BNVAL_DEF;WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
    THEN MATCH_ACCEPT_TAC LVAL_SNOC);;

let BNVAL_WCAT2 = save_thm(`BNVAL_WCAT2`,
   % "!n. !w:(bool)word::PWORDLEN n.
     !x:bool. BNVAL (WCAT (WORD[x],w)) = ((BV x) * (2 EXP n)) + (BNVAL w)" %
    GEN_ALL (RESQ_GEN_ALL (GEN "x:bool"
    (PURE_REWRITE_RULE[GSYM BNVAL_NVAL] (ISPECL ["BV"; "2"; "x:bool"]
     (RESQ_SPEC "w:bool word" (SPEC_ALL NVAL_WCAT2)))))));;

let BNVAL_WCAT = save_thm(`BNVAL_WCAT`,
    GEN_ALL (RESQ_GEN_ALL
    (PURE_REWRITE_RULE[GSYM BNVAL_NVAL] (ISPECL ["BV"; "2"]
     (RESQ_SPECL ["w1:bool word"; "w2:bool word"] (SPEC_ALL NVAL_WCAT))))));;

let VB_DEF = new_definition(`VB_DEF`,
    "VB n = ~((n MOD 2) = 0)");;

% NBWORD n m converts m to n-bit boolean word %
let NBWORD_DEF = new_definition(`NBWORD_DEF`,
    "NBWORD n m = WORD(NLIST n VB 2 m)");;

let NBWORD0 = prove_thm(`NBWORD0`,
    "!m. NBWORD 0 m = WORD[]",
    REWRITE_TAC[NBWORD_DEF;NLIST_DEF]);;

let NLIST_LENGTH = PROVE(
    "!n (f:num->*) b m. LENGTH(NLIST n f b m) = n",
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[NLIST_DEF]
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC]);;

let WORDLEN_NBWORD = prove_thm(`WORDLEN_NBWORD`,
    "!n m. WORDLEN(NBWORD n m) = n",
    REWRITE_TAC[NBWORD_DEF;WORDLEN_DEF;NLIST_LENGTH]);;

let PWORDLEN_NBWORD = prove_thm(`PWORDLEN_NBWORD`,
    "!n m. PWORDLEN n (NBWORD n m)",
    REWRITE_TAC[PWORDLEN;WORDLEN_NBWORD]);;

let NBWORD_SUC = prove_thm(`NBWORD_SUC`,
    "!n m. NBWORD (SUC n) m = WCAT((NBWORD n (m DIV 2)), WORD [VB (m MOD 2)])",
    REPEAT GEN_TAC THEN REWRITE_TAC[NBWORD_DEF;NLIST_DEF]
    THEN MATCH_ACCEPT_TAC WORD_SNOC_WCAT);;

let VB_BV = prove_thm(`VB_BV`, "!x. VB(BV x) = x",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN PURE_ONCE_REWRITE_TAC[VB_DEF] THEN BOOL_CASES_TAC "x:bool"
    THEN CONV_TAC(EVERY_CONV[ONCE_DEPTH_CONV COND_CONV;REDEPTH_CONV num_CONV])
    THEN COND_REWRITE1_TAC LESS_MOD
    THEN REWRITE_TAC[LESS_MONO_EQ;LESS_0;SUC_ID]);;

let BV_VB = prove_thm(`BV_VB`, "!x. x < 2 ==> (BV(VB x) = x)",
    let lem1 = SUBS[SYM (num_CONV "2")] (SPEC "1" LESS_0) in
    let lems = map (\th. MP(REWRITE_RULE[LESS_0] (SPEC "2" th)) lem1)
    	[ZERO_DIV;ZERO_MOD]  in
    CONV_TAC (REDEPTH_CONV num_CONV)
    THEN PURE_REWRITE_TAC[LESS_THM;NOT_LESS_0;OR_CLAUSES;BV_DEF;VB_DEF]
    THEN GEN_TAC THEN  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THENL[
     COND_REWRITE1_TAC LESS_MOD THENL[
      CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC[LESS_MONO_EQ;LESS_0];
      REWRITE_TAC[NOT_SUC]];
     REWRITE_TAC lems]);;

let NBWORD_BNVAL = prove_thm(`NBWORD_BNVAL`,
    "!n. !w::PWORDLEN n. NBWORD n (BNVAL w) = w",
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[BNVAL_DEF;NBWORD_DEF]
    THEN FIRST_ASSUM SUBST1_TAC THEN PURE_ONCE_REWRITE_TAC[WORD_11]
    THEN SPEC_TAC ("l: bool list","l:bool list")
    THEN SNOC_INDUCT_TAC 
    THEN REWRITE_TAC[LVAL_SNOC;LENGTH;LENGTH_SNOC;NLIST_DEF]
    THEN PURE_ONCE_REWRITE_TAC[MATCH_MP DIV_MULT (SPEC "h:bool" BV_LESS_2)]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[SNOC_11] THEN CONJ_TAC THENL[
      PURE_REWRITE_TAC[BV_DEF;VB_DEF]
      THEN COND_REWRITE1_TAC MOD_MOD THENL[
    	CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
        BOOL_CASES_TAC "x:bool" THENL[
          CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
          THEN COND_REWRITE1_TAC MOD_TIMES
    	  THEN COND_REWRITE1_TAC LESS_MOD THENL[
            CONV_TAC (TOP_DEPTH_CONV num_CONV)
    	    THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_EQ]
    	    THEN MATCH_ACCEPT_TAC LESS_0;
    	    REWRITE_TAC[SUC_ID]];
    	  REWRITE_TAC[ADD_0] THEN MATCH_MP_TAC MOD_EQ_0
    	  THEN FIRST_ASSUM ACCEPT_TAC]];
      FIRST_ASSUM ACCEPT_TAC]);;

let BNVAL_NBWORD = prove_thm(`BNVAL_NBWORD`,
    "!n m. (m < (2 EXP n)) ==> (BNVAL (NBWORD n m) = m)",
    let lem1 = SUBS[SYM (num_CONV "2")] (SPEC "1" LESS_0) in
    let lems = map (\th. MP(REWRITE_RULE[LESS_0] (SPEC "2" th)) lem1)
    	[ZERO_DIV;ZERO_MOD]  in
    let lem2 = RESQ_MATCH_MP (SPEC_ALL BNVAL_WCAT1)
     (SPECL ["n:num"; "(SUC m) DIV 2"]PWORDLEN_NBWORD) in
    let lem31,lem32 =
    	  CONJ_PAIR(SPEC "SUC m" (MP (SPEC "2" DIVISION) lem1)) in
    let SUM_LESS = ARITH_PROVE
    	 "!m n p. ((m + n) < p) ==> ((m < p) /\ (n < p))" in
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0;BNVAL_DEF;LVAL];
      PURE_ONCE_REWRITE_TAC[EXP] THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_MONO_EQ;NOT_LESS_0];
      DISCH_TAC THEN PURE_REWRITE_TAC[NBWORD_DEF;NLIST_DEF;BNVAL_DEF;LVAL_SNOC]
      THEN PURE_REWRITE_TAC lems THEN COND_REWRITE1_TAC BV_VB THENL[
    	CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
        FIRST_ASSUM (\t. COND_REWRITE1_TAC (PURE_REWRITE_RULE
    	  [NBWORD_DEF;BNVAL_DEF;LVAL_SNOC](SPEC "0" t))) THENL[
    	  CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	  THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP;
    	  REWRITE_TAC[MULT;ADD_0]]];
      DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
      THEN PURE_ONCE_REWRITE_TAC[lem2]
      THEN COND_REWRITE1_TAC BV_VB THENL[
    	ACCEPT_TAC lem32;
    	FIRST_ASSUM (\t. COND_REWRITE1_TAC (SPEC "(SUC m) DIV 2" t)) THENL[
          ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[LESS_MULT_MONO]
    	    (SUBS_OCCS[[1;3],(num_CONV "2")]
    	    (CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    	    (PURE_REWRITE_RULE[EXP] (CONJUNCT1 (MATCH_MP SUM_LESS
    	    (SUBS [lem31](ASSUME "(SUC m) < (2 EXP (SUC n))")) ))))));
    	  ACCEPT_TAC (SYM lem31)]]]);;

% ZERO_WORD_VAL = |- !w :: PWORDLEN n. (w = NBWORD n 0) = (BNVAL w = 0) %
let ZERO_WORD_VAL = save_thm(`ZERO_WORD_VAL`,
    GEN_ALL (RESQ_GEN_ALL
    (RIGHT_CONV_RULE SYM_CONV (SYM (RIGHT_CONV_RULE SYM_CONV
    (IMP_ANTISYM_RULE
     (DISCH "0 = BNVAL w" (RIGHT_CONV_RULE
       (RESQ_REWRITE1_CONV [] NBWORD_BNVAL)
	 (AP_TERM "NBWORD n" (ASSUME "0 = BNVAL w"))))
     (DISCH_ALL (SUBS[(MP (SPECL ["n:num";"0"] BNVAL_NBWORD) 
	 (SUBS[SYM(num_CONV "2")](SPECL ["n:num"; "1"] ZERO_LESS_EXP)))]
	 (AP_TERM "BNVAL" (ASSUME "NBWORD n 0 = w"))))) )))));;

let WCAT_NBWORD_0 = prove_thm(`WCAT_NBWORD_0`,
    "!n1 n2. WCAT((NBWORD n1 0), (NBWORD n2 0)) = (NBWORD (n1 + n2) 0)",
    let lemma1 = 
      let lem1 = SUBS[SYM (num_CONV "2")] (SPEC "1" LESS_0) in
      let lems = map (\th. MP(REWRITE_RULE[LESS_0] (SPEC "2" th)) lem1)
    	[ZERO_DIV;ZERO_MOD] in
    GEN_ALL(SUBS lems (SPECL ["n:num" ; "0"] NBWORD_SUC)) in
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0;WCAT0;ADD_CLAUSES];
      REWRITE_TAC[NBWORD0;WCAT0;ADD_CLAUSES];
      REWRITE_TAC[NBWORD0;WCAT0;ADD_CLAUSES];
      PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC]
      THEN SUBST_TAC (map (\t.SPEC t lemma1) ["n2:num"; "(SUC n1) + n2"])
      THEN PURE_ONCE_REWRITE_TAC[WCAT_ASSOC]
      THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]]);;

let WSPLIT_NBWORD_0 = save_thm(`WSPLIT_NBWORD_0`,
    let tms = ["NBWORD (n-m) 0"; "NBWORD m 0"] in
    let ths = map (\t. SPECL t PWORDLEN_NBWORD)
       [ ["n-m"; "0"]; ["m:num"; "0"]] in
    GEN_ALL(DISCH_ALL
    (CONV_RULE (ONCE_DEPTH_CONV (COND_REWRITE1_CONV [] SUB_ADD)) 
     (itlist PROVE_HYP ths 
      (PURE_ONCE_REWRITE_RULE[WCAT_NBWORD_0] 
       (RESQ_SPECL tms (SPECL ["n - m"; "m:num"]
        (CONJUNCT2(theorem `word_base` `WORD_PARTITION`)))))))));;

let EQ_NBWORD0_SPLIT = prove_thm(`EQ_NBWORD0_SPLIT`,
    "!n. !w:(bool)word::PWORDLEN n. !m. m <= n ==>
     ((w = NBWORD n 0) = 
      ((WSEG (n-m) m w = NBWORD (n-m) 0) /\
       (WSEG m 0 w = NBWORD m 0)))",
    let lem0 = SPEC_ALL (INST_TYPE [":bool",":*"]
    	(CONJUNCT1(theorem `word_base` `WORD_PARTITION`))) in
    let lem1 = SYM (UNDISCH_ALL (SPEC_ALL (RESQ_SPEC_ALL lem0))) in
    let lem4 = (SPECL["n:num"; "0"] PWORDLEN_NBWORD) in
    let lem3 = SYM (UNDISCH_ALL (SPEC_ALL (RESQ_MATCH_MP lem0 lem4))) in
    let lem2 = UNDISCH_ALL (SPEC "m:num" (RESQ_SPEC "w:bool word"
    	    	 (SPEC_ALL (INST_TYPE [":bool",":*"] WSPLIT_WSEG)))) in
    let lem5 = SPECL ["n-m"; "m:num"] WCAT_11 in
    let lem6 = (RESQ_SPEC "w:(bool)word"(SPEC "n:num" WSEG_PWORDLEN)) in
    let lem7 = UNDISCH_ALL
    	(PURE_ONCE_REWRITE_RULE[ADD_0] (SPECL["m:num";"0"]lem6)) in
    let lem8 = let lem = PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	    	(UNDISCH_ALL (SPECL["n:num";"m:num"]SUB_ADD)) in
    	MP (SUBS[lem ]
    	(PURE_ONCE_REWRITE_RULE[ADD_SYM](SPECL ["n-m";"m:num"] lem6)))
    	 (SPEC "n:num" LESS_EQ_REFL) in
    let [nbwm;nbwn] = map (\tls. SPECL tls PWORDLEN_NBWORD)
    	[["m:num"; "0"]; ["n-m"; "0"]] in
    let lem10 = itlist (\t1 t2. RESQ_MATCH_MP t2 t1)
    	[nbwm; lem7; nbwn; lem8] lem5 in
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN GEN_TAC THEN REPEAT STRIP_TAC
    THEN SUBST_OCCS_TAC[([1],lem1); ([1],lem3)]
    THEN ASSUME_TAC lem4 THEN SUBST1_TAC lem2
    THEN COND_REWRITE1_TAC WSPLIT_NBWORD_0 THEN ACCEPT_TAC lem10);;

let LESS2_DIV2 = PROVE(
    "!r y. 0 < y /\ (r < (2 * y)) ==> ((r DIV 2) < y)",
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0];
      STRIP_TAC THEN COND_REWRITE1_TAC ZERO_DIV THENL[
    	CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
    	FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[NOT_LESS_0];
    PURE_ONCE_REWRITE_TAC[MULT_CLAUSES]
    THEN SUBST_OCCS_TAC[[1],(num_CONV"2")] THEN SUBST1_TAC(num_CONV"1")
    THEN REWRITE_TAC[ADD;LESS_THM] THEN STRIP_TAC THENL[
      POP_ASSUM SUBST1_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
      THEN PURE_ONCE_REWRITE_TAC[MULT_0] THEN DISJ1_TAC
      THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0;LESS_MONO_EQ];
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN MATCH_MP_TAC MULT_DIV THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0];
      POP_ASSUM MP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
      THEN REWRITE_TAC[MULT_0;NOT_LESS_0];
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD1] THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV THENL[
         CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC[LESS_0];
    	 COND_REWRITE1_TAC LESS_DIV_EQ_ZERO THENL[
           CONV_TAC (REDEPTH_CONV num_CONV)
    	   THEN REWRITE_TAC[LESS_0;LESS_MONO_EQ];
    	   MATCH_ACCEPT_TAC ADD_0]];
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN MATCH_MP_TAC MULT_DIV THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0];
      DISJ2_TAC THEN RES_TAC]]);;

let less2 = SUBS[SYM (num_CONV "2")] (SPEC "1" LESS_0);;

let MOD_DIV_lemma = PROVE(
    "!x y. 0 < y ==> (((x MOD (2 * y)) DIV 2) = ((x DIV 2) MOD y))",
    let lem1 = MATCH_MP NOT_MULT_LESS_0 (CONJ less2 (ASSUME "0 < y")) in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN CHOOSE_THEN (CHOOSE_THEN STRIP_ASSUME_TAC)
     (MATCH_MP (SPEC "x:num" DA) lem1)
    THEN SUBST1_TAC (ASSUME "x = (q * (2 * y)) + r")
    THEN PURE_ONCE_REWRITE_TAC[MATCH_MP MOD_MULT (ASSUME "r < (2 * y)")]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV THENL[
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
      PURE_ONCE_REWRITE_TAC [MULT_SYM]
      THEN IMP_RES_THEN (\t. REWRITE_TAC[t]) MOD_TIMES
      THEN IMP_RES_TAC LESS2_DIV2 THEN COND_REWRITE1_TAC LESS_MOD
      THEN REFL_TAC]);;

let NBWORD_MOD = prove_thm(`NBWORD_MOD`,
    "!n m. NBWORD n (m MOD (2 EXP n)) = NBWORD n m",
    let lemma1 = 
    % |- (WCAT
    (NBWORD n((m MOD (2 EXP (SUC n))) DIV 2),
     WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)]) =
    WCAT(NBWORD n(m DIV 2),WORD[VB(m MOD 2)])) =
   (NBWORD n((m MOD (2 EXP (SUC n))) DIV 2) = NBWORD n(m DIV 2)) /\
   (WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)] = WORD[VB(m MOD 2)]) %
        let tms1 = ["NBWORD n((m MOD (2 EXP (SUC n))) DIV 2)";
    	    "NBWORD n(m DIV 2)"] in
        let tms2 = ["WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)]";
    	    "WORD[VB(m MOD 2)]"] in
        let lem1 = RESQ_SPECL (tms1 @ tms2) (SPECL["n:num";"1"] WCAT_11) in
    	let lems2 =
    	    let lm =  GEN_ALL (REWRITE_RULE[LENGTH]
        	(RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) num_CONV)
    		 (SPECL ["1"; "[x:*]"] PWORDLEN_DEF))) in
    	    map (\t. ISPEC (hd (fst (dest_list(snd(dest_comb t))))) lm) tms2 in
        let lems3 =
    	    map (\t. ISPECL (snd (strip_comb t)) PWORDLEN_NBWORD) tms1 in
        (itlist PROVE_HYP (lems2 @ lems3) lem1) in
    INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0];
      REWRITE_TAC[NBWORD_SUC] THEN GEN_TAC
      THEN SUBST1_TAC lemma1 THEN CONJ_TAC THEN PURE_ONCE_REWRITE_TAC[EXP]
      THENL[
    	COND_REWRITE1_TAC MOD_DIV_lemma THENL[
    	  CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	  THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP;
    	  FIRST_ASSUM MATCH_ACCEPT_TAC];
    	COND_REWRITE1_TAC MOD_MULT_MOD THENL[
    	  CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
    	  CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	  THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP;
    	  REFL_TAC]]]);;

let WSEG_NBWORD_SUC = prove_thm(`WSEG_NBWORD_SUC`,
    "!n m. (WSEG n 0(NBWORD (SUC n) m) = NBWORD n m)",
    INDUCT_TAC THENL[
     REWRITE_TAC[NBWORD0;WSEG0];
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
     THEN RESQ_REWRITE1_TAC (SPECL["SUC n"; "1"] WSEG_WCAT_WSEG) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD;
      MATCH_ACCEPT_TAC PWORDLEN1;
      PURE_ONCE_REWRITE_TAC[GSYM ADD1;ADD_0]
      THEN MATCH_ACCEPT_TAC LESS_EQ_SUC_REFL;
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
      CONV_TAC ((RATOR_CONV o RAND_CONV) num_CONV)
      THEN PURE_REWRITE_TAC[ADD_0;LESS_EQ_MONO]
      THEN MATCH_ACCEPT_TAC ZERO_LESS_EQ;
      PURE_REWRITE_TAC[SUB_0;ADD_0;SUC_SUB1]
      THEN PURE_ONCE_ASM_REWRITE_TAC[]
      THEN RESQ_REWRITE1_TAC (SPEC "1" WSEG_WORD_LENGTH)
      THEN REFL_TAC]]);;

let NBWORD_SUC_WSEG = prove_thm(`NBWORD_SUC_WSEG`,
    "!n. !w::PWORDLEN(SUC n). NBWORD n(BNVAL w) = WSEG n 0 w",
    GEN_TAC THEN RESQ_GEN_TAC
    THEN FIRST_ASSUM (\t. SUBST_OCCS_TAC [[1],(RESQ_MATCH_MP
        (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG) t)])
    THEN PURE_ONCE_REWRITE_TAC[BNVAL_NVAL]
    THEN RESQ_IMP_RES_THEN (\t. ASSUME_TAC(REWRITE_RULE[ADD_0;LESS_EQ_SUC_REFL]
    	(SPECL["n:num";"0"] t))) WSEG_PWORDLEN
    THEN FIRST_ASSUM (\t. PURE_ONCE_REWRITE_TAC
    	[(RESQ_MATCH_MP (SPEC_ALL NVAL_WCAT2) t)])
    THEN PURE_ONCE_REWRITE_TAC[GSYM NBWORD_MOD]
    THEN COND_REWRITE1_TAC MOD_MULT THENL[
    	RESQ_IMP_RES_TAC (MATCH_MP NVAL_MAX BV_LESS_2);
    	PURE_ONCE_REWRITE_TAC[GSYM BNVAL_NVAL]
    	THEN RESQ_IMP_RES_TAC NBWORD_BNVAL]);;

let DOUBLE_EQ_SHL = prove_thm(`DOUBL_EQ_SHL`,
    "!n. 0 < n ==>  !w::PWORDLEN n. !b.
     (NBWORD n ((BNVAL w) + (BNVAL w) + (BV b))) = SND(SHL F w b)",
    let WORD1 = REWRITE_RULE[LENGTH] (RIGHT_CONV_RULE(ONCE_DEPTH_CONV num_CONV)
    	(ISPECL ["1"; "[b:bool]"] PWORDLEN_DEF)) in
    let bnval_lem = (SPECL["n:num";"BNVAL w"]PWORDLEN_NBWORD) in
    PURE_ONCE_REWRITE_TAC[ADD_ASSOC;SHL_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM TIMES2;SND]
    THEN PURE_ONCE_REWRITE_TAC[MULT_SYM;COND_CLAUSES]
    THEN INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0;LESS_0]
    THEN RESQ_GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
    THEN PURE_ONCE_REWRITE_TAC (map (\th. MATCH_MP th(SPEC "b:bool" BV_LESS_2))
     [MOD_MULT; DIV_MULT])
    THEN PURE_ONCE_REWRITE_TAC[VB_BV] THEN IMP_RES_THEN SUBST1_TAC PWORDLEN
    THEN PURE_ONCE_REWRITE_TAC[PRE] THEN GEN_TAC
    THEN RESQ_IMP_RES_THEN (\t. ASSUME_TAC(REWRITE_RULE[ADD;LESS_EQ_SUC_REFL]
    	(SPECL["0";"n:num"] t))) WSEG_PWORDLEN
    THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
    THEN RESQ_IMP_RES_TAC NBWORD_SUC_WSEG);;

let MSB_NBWORD = prove_thm(`MSB_NBWORD`,
    "!n m. BIT n (NBWORD (SUC n) m) = VB((m DIV (2 EXP n)) MOD 2)",
    INDUCT_TAC THENL[
     REWRITE_TAC[NBWORD_DEF;NLIST_DEF;EXP;BIT0;
      MULT_CLAUSES;(num_CONV "1");DIV_ONE;SNOC];
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC;EXP]
     THEN RESQ_REWRITE1_TAC (SPECL ["SUC n"; "1"] BIT_WCAT_FST) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD;
      MATCH_ACCEPT_TAC PWORDLEN1;
      CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_EQ_MONO;ZERO_LESS_EQ];
      CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_ADD_SUC];
      ASM_REWRITE_TAC[SUC_SUB1] THEN COND_REWRITE1_TAC DIV_DIV_DIV_MULT THENL[
       CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
       CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP;
       REFL_TAC]]]);;

let ZERO_LESS_TWO_EXP = (GEN_ALL(SUBS[SYM(num_CONV "2")]
    	(SPECL["m:num";"1"]ZERO_LESS_EXP)));;

let NBWORD_SPLIT = prove_thm(`NBWORD_SPLIT`,
    "!n1 n2 m. NBWORD (n1 + n2) m =
     WCAT ((NBWORD n1 (m DIV (2 EXP n2))), (NBWORD n2 m))",
    let exp_lems = 
    	let lm = CONJUNCT2 EXP in
    	(map GSYM [lm; PURE_ONCE_REWRITE_RULE[MULT_SYM]lm]) in
    INDUCT_TAC THENL[
     REWRITE_TAC[ADD;NBWORD0;WCAT0];
     REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[ADD]
     THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
     THEN PURE_ONCE_ASM_REWRITE_TAC[]
     THEN PURE_ONCE_REWRITE_TAC[GSYM WCAT_ASSOC]
     THEN COND_REWRITE1_TAC DIV_DIV_DIV_MULT THENL[
      MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP;
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
      PURE_ONCE_REWRITE_TAC exp_lems
      THEN PURE_ONCE_REWRITE_TAC (map GSYM [NBWORD_SUC; MSB_NBWORD])
      THEN SUBST1_TAC (SYM (SPECL ["n2:num";"m:num"] WSEG_NBWORD_SUC))
      THEN RESQ_REWRITE1_TAC (GSYM WORDLEN_SUC_WCAT_BIT_WSEG) THENL[
       MATCH_ACCEPT_TAC PWORDLEN_NBWORD;
       REFL_TAC]]]);;

let WSEG_NBWORD = prove_thm(`WSEG_NBWORD`,
    "!m k n.  (m + k) <= n ==> 
     (!l. WSEG m k(NBWORD n l) = NBWORD m (l DIV (2 EXP k)))",
    let lem1 = CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD) 
    	(SPECL["n-k"; "k:num"; "l:num"]NBWORD_SPLIT) in
    let lem2 = CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD) 
    	(SPECL["(n-k)-m"; "m:num"]NBWORD_SPLIT) in
    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQ_SPLIT THEN SUBST1_TAC lem1
    THEN RESQ_REWRITE1_TAC (SPECL["n-k"; "k:num"]WSEG_WCAT_WSEG1) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD;
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD;
      COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB) THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_ACCEPT_TAC LESS_EQ_REFL;
      PURE_ONCE_REWRITE_TAC[SUB_EQUAL_0]
      THEN PURE_ONCE_REWRITE_TAC [lem2]
      THEN RESQ_REWRITE1_TAC (SPECL["(n-k)-m"; "m:num"]WSEG_WCAT2)
      THEN TRY (MATCH_ACCEPT_TAC PWORDLEN_NBWORD)
      THEN REFL_TAC]);;

% NBWORD_SUC_FST = 
|- !n m.
    NBWORD(SUC n)m = WCAT(WORD[VB((m DIV (2 EXP n)) MOD 2)],NBWORD n m) %
let NBWORD_SUC_FST = save_thm(`NBWORD_SUC_FST`,
    GEN_ALL (REWRITE_RULE[ADD](REWRITE_RULE[NBWORD_SUC;NBWORD0;WCAT0]
    (SUBS[num_CONV"1"](SPECL["1"; "n:num"] NBWORD_SPLIT)))));;

let BIT_NBWORD0 = prove_thm(`BIT_NBWORD0`,
    "!k n. k < n ==> (BIT k (NBWORD n 0) = F)",
    let les1 = SUBS[SYM (num_CONV "1")](SPEC"0"LESS_SUC_REFL) in
    let les2 = SUBS[SYM (num_CONV "2")](SPEC"1"LESS_0) in
    let lem1 = REWRITE_RULE[ADD;les1]
    	(PROVE_HYP (SPECL ["n:num";"0"]PWORDLEN_NBWORD) 
     	 (GQSPECL["n:num";"NBWORD n 0";"1";"k:num";"0"]BIT_WSEG)) in
    let mod_lem = (MP (SPEC "2" MOD_MOD) les2) in
    REPEAT STRIP_TAC THEN COND_REWRITE1_TAC (GSYM lem1) THENL[
     ARITH_TAC;
     RESQ_REWRITE1_TAC WSEG_NBWORD THEN COND_REWRITE1_TAC ZERO_DIV THENL[
      MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP;
      SUBST1_TAC (num_CONV "1") THEN PURE_ONCE_REWRITE_TAC[MSB_NBWORD]
      THEN REWRITE_TAC [EXP;(num_CONV "1");DIV_ONE;VB_DEF]
      THEN COND_REWRITE1_TAC MOD_MOD THENL[
       CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
       COND_REWRITE1_TAC LESS_MOD THEN REFL_TAC]]]);;

let add_lem = PROVE(
    "!m1 m2 n1 n2 p. (((m1 * p) + n1)  + ((m2 * p) + n2) =
    	((m1 * p) + (m2 * p)) + (n1 + n2))",
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN PURE_ONCE_REWRITE_TAC[EQ_MONO_ADD_EQ]
    THEN CONV_TAC (AC_CONV(ADD_ASSOC,ADD_SYM)));;

let ADD_BNVAL_LEFT = prove_thm(`ADD_BNVAL_LEFT`,
    "!n. !w1 w2:bool word::PWORDLEN (SUC n).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BV (BIT n w1)) + (BV (BIT n w2))) * (2 EXP n)) +
       ((BNVAL (WSEG n 0 w1)) + (BNVAL (WSEG n 0 w2)))",
    let mk_lem = 
    	let lem = SPEC_ALL WSEG_PWORDLEN in
    	let lem2 = SPEC_ALL BNVAL_WCAT2 in
    	\t. RESQ_MATCH_MP lem2
    	    (REWRITE_RULE[ADD_0;LESS_EQ_SUC_REFL] (SPECL["n:num"; "0"]
    	    (RESQ_MATCH_MP lem t))) in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM (\t.SUBST_OCCS_TAC [[1],
    		(RESQ_MATCH_MP (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG) t)])
    THEN EVERY_ASSUM ((\t.REWRITE_TAC[t]) o mk_lem)
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]);;

let ADD_BNVAL_RIGHT = prove_thm(`ADD_BNVAL_RIGHT`,
    "!n. !w1 w2:bool word::PWORDLEN (SUC n).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BNVAL (WSEG n 1 w1)) + (BNVAL (WSEG n 1 w2))) * 2) +
       ((BV (BIT 0 w1)) + (BV (BIT 0 w2))) ",
    let mk_lem = 
    	let lem = SPEC_ALL WSEG_PWORDLEN in
    	let lem2 = SPEC_ALL BNVAL_WCAT1 in
    	\t. RESQ_MATCH_MP lem2
    	    (REWRITE_RULE[(GSYM ADD1);LESS_EQ_REFL] (SPECL["n:num"; "1"]
    	    (RESQ_MATCH_MP lem t))) in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM (\t.SUBST_OCCS_TAC [[1],
	(RESQ_MATCH_MP (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT) t)])
    THEN EVERY_ASSUM ((\t.REWRITE_TAC[t]) o mk_lem)
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]);;

let ADD_BNVAL_SPLIT = prove_thm(`ADD_BNVAL_SPLIT`,
    "!n1 n2. !w1 w2:bool word::PWORDLEN (n1 + n2).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BNVAL (WSEG n1 n2 w1)) + (BNVAL (WSEG n1 n2 w2))) * (2 EXP n2)) +
       ((BNVAL (WSEG n2 0 w1)) + (BNVAL (WSEG n2 0 w2)))",
    let seg_lem = PURE_ONCE_REWRITE_RULE[ADD_SYM](RESQ_GEN_ALL (SYM (TRANS    
    	(REWRITE_RULE[LESS_EQ_REFL] 
    	  (PURE_ONCE_REWRITE_RULE[ADD_0](SPECL ["n2:num"; "n1:num"; "0"] 
    	 (RESQ_SPEC_ALL (SPEC "n2 + n1" WCAT_WSEG_WSEG)))))
        (RESQ_SPEC_ALL (SPEC "n2 + n1" WSEG_WORD_LENGTH))))) in
    let lem = SPEC_ALL WSEG_PWORDLEN in
    let lem2 = SPECL ["n1:num"; "n2:num"] BNVAL_WCAT in
    let LESS_EQ_ADD2 = PURE_ONCE_REWRITE_RULE[ADD_SYM]LESS_EQ_ADD in
    REPEAT GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM (\t.SUBST_OCCS_TAC [[1], (RESQ_MATCH_MP seg_lem t)])
    THEN RESQ_REWRITE1_TAC lem2
    THEN TRY
    	(RULE_ASSUM_TAC (RESQ_MATCH_MP lem) THEN FIRST_ASSUM MATCH_MP_TAC
    	 THEN REWRITE_TAC[ADD_0;LESS_EQ_ADD2;LESS_EQ_REFL])
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]);;

close_theory();;