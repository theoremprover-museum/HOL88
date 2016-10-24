% ===================================================================== %
% FILE: mk_bword_bitop.ml	    DATE: 14 Aug 1992			%
% AUTHOR: Wai WONG  	    	    					%
% Writes: bword_bitop.th	    	    				%
% Uses: Libraries: arith res_quan					%
% Description: Creates a theorey for boolean word bitwise operations	%
% ===================================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

loadt(`ver_`^(string_of_int(version())));;

loadf`arith_thms`;;

load_theory `word_bitop`;;
map autoload_all [`word_base`; `word_bitop`];;

new_theory`bword_bitop`;;

loadf`word_funs`;;

% --------------------------------------------------------------------- %
% We begin with some lemmas about lists. They are used in the proofs.	%
% --------------------------------------------------------------------- %

let MAP2_SNOC = PROVE(
    "!(f:*->**->***) h1 h2 l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (MAP2 f(SNOC h1 l1)(SNOC h2 l2) = SNOC(f h1 h2)(MAP2 f l1 l2))",
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN EQ_LENGTH_INDUCT_TAC THENL[
      REWRITE_TAC[SNOC;MAP2];
      REWRITE_TAC[LENGTH;INV_SUC_EQ;SNOC;MAP2;CONS_11]
      THEN REPEAT STRIP_TAC THEN RES_TAC]);;

let BUTLASTN_MAP2 = PROVE(
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> !n. (n <= LENGTH l1) ==>
     !(f:*->**->***).
      BUTLASTN n (MAP2 f l1 l2) = MAP2 f (BUTLASTN n l1) (BUTLASTN n l2)",
    let lem1 = ARITH_PROVE "!n. n <= 0 ==> (n = 0)" in
    EQ_LENGTH_SNOC_INDUCT_TAC THENL[
      PURE_ONCE_REWRITE_TAC[LENGTH] THEN GEN_TAC
      THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP lem1))
      THEN REWRITE_TAC[BUTLASTN;MAP2];
      INDUCT_TAC THEN REWRITE_TAC[BUTLASTN;MAP2_SNOC;LESS_EQ_MONO]
      THEN IMP_RES_THEN (\t.PURE_REWRITE_TAC[t]) MAP2_SNOC
      THEN REWRITE_TAC[BUTLASTN] THEN DISCH_TAC THEN RES_TAC]);;

let LASTN_MAP2 = PROVE(
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> !n. (n <= LENGTH l1) ==>
     !(f:*->**->***). 
      LASTN n (MAP2 f l1 l2) = MAP2 f (LASTN n l1) (LASTN n l2)",
    let lem1 = ARITH_PROVE "!n. n <= 0 ==> (n = 0)" in
    EQ_LENGTH_SNOC_INDUCT_TAC THENL[
      GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
      THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP lem1))
      THEN REWRITE_TAC[LASTN;MAP2];
      INDUCT_TAC THEN REWRITE_TAC[LASTN;MAP2;LESS_EQ_MONO]
      THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC MAP2_SNOC THENL[
    	COND_REWRITE1_TAC LENGTH_LASTN THEN TRY REFL_TAC
    	THEN FIRST_ASSUM (SUBST1_TAC o SYM)
    	THEN FIRST_ASSUM ACCEPT_TAC;
    	REWRITE_TAC[LASTN;SNOC_11] THEN RES_TAC
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;


% --------------------------------------------------------------------- %
% WNOT	    	    	    	    					%
% --------------------------------------------------------------------- %

let WNOT_DEF = new_recursive_definition false word_Ax `WNOT_DEF`
    "WNOT (WORD l) = WORD(MAP $~ l)";;

let BIT_WNOT_SYM_lemma = TAC_PROOF(([],
     "!n. !w:(bool)word ::PWORDLEN n. PWORDLEN n (WNOT w) /\
      !m k. ((m + k) <= n) ==> (WNOT(WSEG m k w) = WSEG m k (WNOT w))"),
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN PURE_ASM_REWRITE_TAC
    	[PWORDLEN_DEF;WNOT_DEF;WSEG_DEF;LENGTH_MAP;WORD_11]
    THEN CONJ_TAC THENL[
      REFL_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC
      THEN FIRST_ASSUM (ASSUME_TAC o CONJUNCT2 o (MATCH_MP LESS_EQ_SPLIT))
      THEN COND_REWRITE1_TAC BUTLASTN_MAP THENL[
    	IMP_RES_TAC LESS_EQ_SPLIT;
        COND_REWRITE1_TAC LASTN_MAP THENL[
          COND_REWRITE1_TAC LENGTH_BUTLASTN
          THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
          THEN FIRST_ASSUM ACCEPT_TAC;
    	  REFL_TAC]]]);;

% PBITOP_WNOT = |- PBITOP WNOT %

let PBITOP_WNOT = save_thm(`PBITOP_WNOT`,
    EQT_ELIM (TRANS (ISPEC "WNOT" PBITOP_DEF)
     (EQT_INTRO BIT_WNOT_SYM_lemma)));;

let WNOT_WNOT = prove_thm(`WNOT_WNOT`,
    "!w. WNOT(WNOT w) = w",
    word_INDUCT_TAC THEN PURE_REWRITE_TAC[WNOT_DEF]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP;WORD_11;CONS_11]
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[WORD_11])));;

let WCAT_WNOT = prove_thm(`WCAT_WNOT`,
    "!n1 n2 . !w1:(bool)word::PWORDLEN n1. !w2:(bool)word::PWORDLEN n2.
     WCAT ((WNOT w1), (WNOT w2)) =  (WNOT (WCAT (w1,w2)))",
    REPEAT GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN MAP_EVERY word_CASES_TAC ["w1:(bool)word"; "w2:(bool)word"]
    THEN REWRITE_TAC[WCAT_DEF;WNOT_DEF;MAP_APPEND]);;

% let LENGTH_MAP21 = GEN_ALL (DISCH_ALL (CONJUNCT1 (SPEC_ALL (UNDISCH_ALL
    (SPEC_ALL LENGTH_MAP2)))));;
%
let LENGTH_MAP22 = GEN_ALL (DISCH_ALL (CONJUNCT2 (SPEC_ALL (UNDISCH_ALL
    (SPEC_ALL LENGTH_MAP2)))));;

% --------------------------------------------------------------------- %
% WAND	    	    	    	    					%
% --------------------------------------------------------------------- %
% WAND_DEF = |- !l1 l2. WAND(WORD l1)(WORD l2) = WORD(MAP2 $/\ l1 l2) %

let WAND_DEF = new_specification `WAND_DEF`
    [`infix`, `WAND`] (ISPEC "$/\" PBITBOP_EXISTS);;

let PBITBOP_WAND_lemma = PROVE(
    "!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WAND w2)) /\
     !m k. ((m + k) <= n) ==>
     (WAND (WSEG m k w1) (WSEG m k w2) = WSEG m k (WAND w1 w2))",
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF;WAND_DEF;WORD_11;WSEG_DEF]
    THEN CONJ_TAC THENL[
     POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC (GSYM LENGTH_MAP22)
     THEN FIRST_ASSUM ACCEPT_TAC;
     POP_ASSUM (\t. RULE_ASSUM_TAC (TRANS (SYM t)))
     THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM);
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT;
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC];
       COND_REWRITE1_TAC LENGTH_BUTLASTN
       THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
       THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       REFL_TAC]]]);;

let PBITBOP_WAND = save_thm(`PBITBOP_WAND`,
    EQT_ELIM (TRANS (ISPEC "WAND" PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WAND_lemma)));;

% --------------------------------------------------------------------- %
% WOR	    	    	    	    					%
% --------------------------------------------------------------------- %
% WOR_DEF = |- !l1 l2. WOR(WORD l1)(WORD l2) = WORD(MAP2 $\/ l1 l2)   %

let WOR_DEF = new_specification `WOR_DEF`
    [`infix`, `WOR`] (ISPEC "$\/" PBITBOP_EXISTS);;

let PBITBOP_WOR_lemma = PROVE(
    "!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WOR w2)) /\
     !m k. ((m + k) <= n) ==>
     (WOR (WSEG m k w1) (WSEG m k w2) = WSEG m k (WOR w1 w2))",
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF;WOR_DEF;WORD_11;WSEG_DEF]
    THEN CONJ_TAC THENL[
     POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC (GSYM LENGTH_MAP22)
     THEN FIRST_ASSUM ACCEPT_TAC;
     POP_ASSUM (\t. RULE_ASSUM_TAC (TRANS (SYM t)))
     THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM);
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT;
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC];
       COND_REWRITE1_TAC LENGTH_BUTLASTN
       THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
       THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       REFL_TAC]]]);;

let PBITBOP_WOR = save_thm(`PBITBOP_WOR`,
    EQT_ELIM (TRANS (ISPEC "WOR" PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WOR_lemma)));;

% --------------------------------------------------------------------- %
% WXOR	    	    	    	    					%
% --------------------------------------------------------------------- %
% |- !l1 l2. WXOR(WORD l1)(WORD l2) = WORD(MAP2(\x y. ~(x = y))l1 l2) %

let WXOR_DEF = new_specification `WXOR_DEF`
    [`infix`, `WXOR`] (ISPEC "(\x y:bool. ~(x = y))" PBITBOP_EXISTS);;

let PBITBOP_WXOR_lemma = PROVE(
    "!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WXOR w2)) /\
     !m k. ((m + k) <= n) ==>
     (WXOR (WSEG m k w1) (WSEG m k w2) = WSEG m k (WXOR w1 w2))",
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF;WXOR_DEF;WORD_11;WSEG_DEF]
    THEN CONJ_TAC THEN POP_ASSUM SUBST_ALL_TAC THENL[
     MATCH_MP_TAC (GSYM LENGTH_MAP22) THEN FIRST_ASSUM ACCEPT_TAC;
     REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM);
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT;
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC];
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
        THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
       REFL_TAC]]]);;

let PBITBOP_WXOR = save_thm(`PBITBOP_WXOR`,
    EQT_ELIM (TRANS (ISPEC "WXOR" PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WXOR_lemma)));;

close_theory();;

