% ===================================================== %
% FILE: mk_word_base.ml	    DATE: 31 July 1992		%
% AUTHOR: Wai WONG  	    	    			%
% Writes: word_base.th	    	    			%
% Uses: Libraries: arith res_quan 			%
% Description: Creates a theorey for generic words	%
% ===================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

loadt(`ver_`^(string_of_int(version())));;

loadt`arith_thms`;; 

new_theory`word_base`;;

% --------------------------------------------------------------------- %
% We begin with some lemmas about lists. They are used in the proofs.	%
% --------------------------------------------------------------------- %

let ELL_LASTN = PROVE(
    "!(l:(*)list) m j. (m <= LENGTH l) ==> (j < m) ==>
     (ELL j (LASTN m l) = ELL j l)",
    let tac1 = (PURE_ONCE_REWRITE_TAC[ADD_SYM]
    	THEN IMP_RES_THEN SUBST1_TAC SUB_ADD 
    	THEN MATCH_ACCEPT_TAC LESS_EQ_REFL) in
    let ADD_PRE = PROVE("!m n. 0 < n ==> (m + (PRE n) = PRE (m + n))",
    	REPEAT INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES;PRE;NOT_LESS_0]) in
    REPEAT STRIP_TAC THEN COND_REWRITE1_TAC LASTN_SEG
    THEN COND_REWRITE1_TAC ELL_SEG THENL[
      COND_REWRITE1_TAC LENGTH_SEG
      THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN tac1;
      FIRST_ASSUM  (\t. DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC
    	    	    (REWRITE_RULE[LESS_OR_EQ]t)) THENL[
    	IMP_RES_TAC LESS_TRANS;
    	FIRST_ASSUM ACCEPT_TAC];
      AP_TERM_TAC THEN COND_REWRITE1_TAC SEG_SEG THEN TRY tac1
      THEN COND_REWRITE1_TAC LENGTH_SEG THEN TRY tac1 THENL[
    	PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
    	THEN COND_REWRITE1_TAC SUB_ADD THENL[
    	  CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_MP_TAC LESS_OR
    	  THEN IMP_RES_TAC SUB_LESS_0;
    	  MATCH_ACCEPT_TAC SUB_LESS_EQ];
    	IMP_RES_TAC SUB_LESS_0 THEN COND_REWRITE1_TAC ADD_PRE
    	THEN SUBST_OCCS_TAC [[2],
    	    (SYM(UNDISCH_ALL(SPECL["LENGTH(l:* list)";"m:num"]SUB_ADD)))]
    	THEN COND_REWRITE1_TAC ADD_SUB_LEM THEN REFL_TAC]]);;
%wa %
let ELL_BUTLASTN = PROVE(
    "!(l:(*)list) k j. ((j+k)<= LENGTH l) ==>
     (ELL j (BUTLASTN k l) = ELL (j+k) l)",
    SNOC_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH;LENGTH_SNOC] THENL[
     REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP LESS_EQ_0_EQ))
     THEN PURE_ONCE_REWRITE_TAC[ADD_EQ_0]
     THEN DISCH_THEN (SUBST_TAC o CONJUNCTS)
     THEN REWRITE_TAC[BUTLASTN;ADD_0];
     GEN_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[BUTLASTN;ADD_0];
      PURE_REWRITE_TAC[BUTLASTN;ELL_SUC_SNOC;ADD_CLAUSES;LESS_EQ_MONO]
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

%wa %
let APPEND_LASTN_LASTN = PROVE(
    "!l:* list. !m1 m2. ((m1 + m2) <= (LENGTH l)) ==>
     (APPEND (LASTN m2 (BUTLASTN m1 l)) (LASTN m1 l) = LASTN (m1 + m2) l)",
    SNOC_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH;LENGTH_SNOC] THENL[
      REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC LESS_EQ_0_EQ
      THEN PURE_ONCE_REWRITE_TAC[ADD_EQ_0]
      THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)
      THEN REWRITE_TAC[LASTN;ADD_0;APPEND_NIL];
      GEN_TAC THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC[BUTLASTN;LASTN;APPEND_NIL;ADD;ADD_0]
      THEN REWRITE_TAC[APPEND_SNOC;LESS_EQ_MONO;SNOC_11]
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

%wa %
let LASTN_BUTLASTN_APPEND = PROVE(
    "!(l1:* list) l2 m k. (m + k) <= ((LENGTH l1) + (LENGTH l2)) /\
      k < (LENGTH l2) /\ (LENGTH l2) <= (m + k) ==>
     (LASTN m(BUTLASTN k(APPEND l1 l2)) =
      (APPEND (LASTN((m + k) - (LENGTH l2)) l1)
    	      (LASTN((LENGTH l2) - k)(BUTLASTN k l2))))",

    LIST_INDUCT_TAC THENL[
      REPEAT GEN_TAC THEN PURE_REWRITE_TAC[LENGTH;ADD;APPEND;APPEND_NIL]
      THEN STRIP_TAC THEN IMP_RES_TAC LESS_EQUAL_ANTISYM
      THEN POP_ASSUM SUBST1_TAC THEN POP_ASSUM (\t. SUBST_OCCS_TAC[[3],t])
      THEN REWRITE_TAC[SUB_EQUAL_0;ADD_SUB;LASTN;APPEND;APPEND_NIL];

      GEN_TAC THEN SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH;NOT_LESS_0];

    	GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL[
    	  PURE_REWRITE_TAC[SUB_0;ADD_0;BUTLASTN;LASTN_LENGTH_ID]
    	  THEN STRIP_TAC 
    	  THEN FIRST_ASSUM (\t. REWRITE_TAC[MATCH_MP LASTN_APPEND1 t]);

    	  PURE_ONCE_REWRITE_TAC[APPEND_SNOC]
    	  THEN PURE_ONCE_REWRITE_TAC[BUTLASTN]
    	  THEN PURE_ONCE_REWRITE_TAC[LENGTH;LENGTH_SNOC]
    	  THEN PURE_REWRITE_TAC[ADD_CLAUSES;SUB_MONO_EQ;
    	    LESS_MONO_EQ;LESS_EQ_MONO]
    	  THEN STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_APPEND2 THENL[
    	    IMP_RES_TAC LESS_IMP_LESS_OR_EQ;
    	    COND_REWRITE1_TAC LASTN_APPEND1
    	    THEN COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
    	      COND_REWRITE1_TAC SUB_LESS_EQ_ADD
    	      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    	      THEN FIRST_ASSUM ACCEPT_TAC;
     	      COND_REWRITE1_TAC SUB_SUB
    	      THEN COND_REWRITE1_TAC LASTN_BUTLASTN THENL[
    	    	COND_REWRITE1_TAC SUB_ADD
    	    	THEN MATCH_ACCEPT_TAC LESS_EQ_REFL;
    	    	COND_REWRITE1_TAC SUB_ADD
    	    	THEN REWRITE_TAC[LASTN_LENGTH_ID]]]]]]]);;


% --------------------------------------------------------------------- %
% Define a polymorphic type of (*)word. It is represented by a list	%
% word_Ax |- !f. ?! fn. !l. fn(WORD l) = f l				%
% --------------------------------------------------------------------- %

let word_Ax = define_type `word_Ax`
    `word = WORD (*)list`;;

% --------------------------------------------------------------------- %
% Some basic theorems about the type (*)word				%
% --------------------------------------------------------------------- %

% WORD_11 |- !l l'. (WORD l = WORD l') = (l = l')			%
let WORD_11 = save_thm(`WORD_11`, prove_constructors_one_one word_Ax);;

% word_induct |- !P. (!l. P(WORD l)) ==> (!w. P w)			%
let word_induct = save_thm(`word_induct`, prove_induction_thm word_Ax);;

% word_cases |- !w. ?l. w = WORD l  					%
let word_cases = save_thm(`word_cases`, prove_cases_thm word_induct);;

% --------------------------------------------------------------------- %
% Define some bit accessing functions					%
% --------------------------------------------------------------------- %
%<
let BITS_DEF =  new_recursive_definition false word_Ax `BITS_DEF`
   "BITS ((WORD l):* word) = l";;

let WORD_BITS = prove_thm(`WORD_BITS`,
    "!w:(*)word. WORD(BITS w) = w",
    GEN_TAC THEN word_CASES_TAC "w:(*)word" THEN REWRITE_TAC[BITS_DEF]);;
>%

% word length is the number of bits 					%
let WORDLEN_DEF = new_recursive_definition false word_Ax `WORDLEN_DEF`
   "WORDLEN ((WORD l):* word) = LENGTH l";;

% This is true if the argument word is of length n.			%
let PWORDLEN_DEF = new_recursive_definition false word_Ax `PWORDLEN_DEF`
   "PWORDLEN n ((WORD l):* word) = (n = LENGTH l)";;

loadt`word_funs`;;

let PWORDLEN = prove_thm(`PWORDLEN`,
    "!n. !w:(*)word. PWORDLEN n w = (WORDLEN w = n)",
    GEN_TAC THEN word_INDUCT_TAC
    THEN PURE_REWRITE_TAC[WORDLEN_DEF;PWORDLEN_DEF] THEN GEN_TAC
    THEN EQ_TAC THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let PWORDLEN0 = prove_thm(`PWORDLEN0`,
    "!w:(*)word. PWORDLEN 0 w ==> (w = WORD[])",
    word_INDUCT_TAC THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WORD_11]
    THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC;LENGTH]);;

% PWORDLEN1 = |- !x. PWORDLEN 1(WORD[x]) %
let PWORDLEN1 = save_thm(`PWORDLEN1`, GEN_ALL(REWRITE_RULE[LENGTH]
    (RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) num_CONV)
    (SPECL[ "1"; "[x:*]"] PWORDLEN_DEF))));;

% --------------------------------------------------------------------- %
% The convention on index of bits is:					%
%  a) numbered from right to left, b) starting with 0			%
% eg. (bn-1, ..., b1, b0) is a n-bit word				%
%   	    	    	    	    					%
% The main function for fetching bits from a word is WSEG:		%
% WSEG :num -> num -> (*)word -> (*)word					%
% WSEG m k (bn-1, ..., bm+k, bm+k-1,...,bk,...,b0) = (bm+k-1,...,bk)	%
% --------------------------------------------------------------------- %

let WSEG_DEF = new_recursive_definition false word_Ax `WSEG_DEF`
    "WSEG m k ((WORD l):* word) = WORD (LASTN m (BUTLASTN k l))";;

let WSEG0 = prove_thm(`WSEG0`,
    "!k (w:* word). WSEG 0 k w = WORD[]",
    GEN_TAC THEN word_INDUCT_TAC THEN REWRITE_TAC[WSEG_DEF;LASTN]);;

let WSEG_PWORDLEN = prove_thm(`WSEG_PWORDLEN`,
    "!n. !w:(*)word::PWORDLEN n.
     !m k. ((m + k) <= n) ==> PWORDLEN m (WSEG m k w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC 
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WSEG_DEF]
    THEN DISCH_THEN SUBST1_TAC THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV
    THEN MATCH_MP_TAC LENGTH_LASTN THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN COND_REWRITE1_TAC LENGTH_BUTLASTN
    THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
    THEN FIRST_ASSUM ACCEPT_TAC);;

% WSEG_WORDLEN = 
|- !n. !w :: PWORDLEN n. !m k. (m + k) <= n ==> (WORDLEN(WSEG m k w) = m) %
let WSEG_WORDLEN = save_thm(`WSEG_WORDLEN`,
    PURE_ONCE_REWRITE_RULE[PWORDLEN]WSEG_PWORDLEN);;

let WSEG_WORD_LENGTH = prove_thm(`WSEG_WORD_LENGTH`,
    "!n. !w:(*)word::PWORDLEN n. (WSEG n 0 w = w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PWORDLEN_DEF;WSEG_DEF]
    THEN DISCH_THEN SUBST1_TAC
    THEN REWRITE_TAC[BUTLASTN;LASTN_LENGTH_ID]);;

% --------------------------------------------------------------------- %
% BIT :num -> (*)word -> *  	    					%
% BIT k (bn-1,...bk, ...,b0) = bk   					%
% --------------------------------------------------------------------- %

let BIT_DEF =  new_recursive_definition false word_Ax `BIT_DEF`
   "BIT k ((WORD l):* word) = ELL k l";;

let BIT0 = prove_thm(`BIT0`,
    "!b:*. BIT 0 (WORD[b]) = b",
    REWRITE_TAC[BIT_DEF;ELL;LAST;(GSYM(CONJUNCT1 SNOC))]);;

let WSEG_BIT = prove_thm(`WSEG_BIT`,
    "!n. !w:(*)word::(PWORDLEN n).
     !k.(k < n) ==> (WSEG 1 k w = WORD[BIT k w])",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC 
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WSEG_DEF;BIT_DEF;WORD_11]
    THEN DISCH_THEN SUBST1_TAC THEN SPEC_TAC("l:* list","l:* list")
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH;LENGTH_SNOC;NOT_LESS_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[LESS_MONO_EQ;BUTLASTN;ELL;LAST;BUTLAST]
    THENL[
    	CONV_TAC (ONCE_DEPTH_CONV  num_CONV)
    	THEN REWRITE_TAC[LAST;LASTN;SNOC];
    	FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let BIT_WSEG = prove_thm(`BIT_WSEG`,
    "!n. !w:(*)word::(PWORDLEN n). !m k j. ((m + k) <= n) ==> (j < m) ==>
     (BIT j(WSEG m k w) = BIT (j + k) w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WSEG_DEF;BIT_DEF;WORD_11]
    THEN DISCH_THEN SUBST1_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL o(MATCH_MP LESS_EQ_SPLIT))
    THEN DISCH_TAC THEN  COND_REWRITE1_TAC ELL_LASTN THENL[
      COND_REWRITE1_TAC LENGTH_BUTLASTN
      THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
      THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC ELL_BUTLASTN
      THEN FIRST_ASSUM (ASSUME_TAC o (MP
    	 (snd(EQ_IMP_RULE(SPECL["j:num";"m:num";"k:num"]LESS_MONO_ADD_EQ)))))
      THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN IMP_RES_TAC LESS_EQ_TRANS]);;

% --------------------------------------------------------------------- %
% MSB (bn-1,...,b0) = bn-1  	    					%
% --------------------------------------------------------------------- %

let MSB_DEF =  new_recursive_definition false word_Ax `MSB_DEF`
   "MSB ((WORD l):* word) = HD l";;

let MSB = prove_thm(`MSB`,
    "!n. !w:(*)word::PWORDLEN n. (0 < n) ==> (MSB w = BIT (PRE n) w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PWORDLEN_DEF;MSB_DEF;BIT_DEF]
    THEN DISCH_THEN SUBST1_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_NOT_NULL]
    THEN PURE_ONCE_REWRITE_TAC[NULL_EQ_NIL]
    THEN CONV_TAC (RAND_CONV SYM_CONV)
    THEN MATCH_ACCEPT_TAC ELL_PRE_LENGTH);;

% --------------------------------------------------------------------- %
% LSB (bn-1,...,b0) = b0  	    					%
% --------------------------------------------------------------------- %

let LSB_DEF =  new_recursive_definition false word_Ax `LSB_DEF`
   "LSB ((WORD l):* word) = LAST l";;

let LSB = prove_thm(`LSB`,
    "!n. !w:(*)word::PWORDLEN n. (0 < n) ==> (LSB w = BIT 0 w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PWORDLEN_DEF;LSB_DEF;BIT_DEF]
    THEN DISCH_THEN SUBST1_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_NOT_NULL]
    THEN DISCH_TAC THEN CONV_TAC SYM_CONV
    THEN IMP_RES_TAC ELL_LAST);;

% --------------------------------------------------------------------- %
% WSPLIT : num -> (*)word -> ((*)word # (*)word)			%
% WSPLIT k (bn-1, ...,bk, ..., b0) = (bn-1,...,bk),(bk-1,...,b0)	%
% --------------------------------------------------------------------- %

let WSPLIT_DEF = new_recursive_definition false word_Ax `WSPLIT_DEF`
    "WSPLIT m ((WORD l):* word) =
     WORD(BUTLASTN m l), WORD(LASTN m l)";;

% --------------------------------------------------------------------- %
% WCAT : ((*)word # (*)word) ->  (*)word 				%
% WCAT (an-1,...,a0),(bk-1,...,b0) = (an-1,...,a0,bk-1,...,b0) 	%
% --------------------------------------------------------------------- %

let th = prove_rec_fn_exists word_Ax "bt (WORD l) = (l:* list)";;

let word_bits = PROVE(
    "?bt. (!l:* list. bt(WORD l) = l) /\ (!w:* word. WORD (bt w) = w)",
    CHOOSE_TAC th THEN EXISTS_TAC "bt:(*)word -> (*)list"
    THEN CONJ_TAC THENL[
      FIRST_ASSUM ACCEPT_TAC;
      word_INDUCT_TAC THEN ASM_REWRITE_TAC[]]);;

let WCAT_lemma = PROVE(
    "?WCAT. !l1 l2:(*)list.
     WCAT ((WORD l1), (WORD l2)) = WORD (APPEND l1 l2)",
    let th = prove_rec_fn_exists word_Ax "bt (WORD l) = (l:* list)" in
    CHOOSE_THEN STRIP_ASSUME_TAC th THEN EXISTS_TAC
        "\(w1:(*)word,w2:(*)word).WORD(APPEND(bt w1)((bt w2):* list))"
    THEN REPEAT GEN_TAC THEN CONV_TAC (LHS_CONV PAIRED_BETA_CONV)
    THEN ASM_REWRITE_TAC[]);;

let WCAT_DEF = new_specification `WCAT_DEF`
    [`constant`,`WCAT`] WCAT_lemma;;

let WCAT_WSPLIT = TAC_PROOF(([],
  "!n. !w:(*)word::(PWORDLEN n). !m. (m <= n) ==> (WCAT(WSPLIT m w) = w)"),
    INDUCT_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WSPLIT_DEF;WCAT_DEF] THENL[
      REWRITE_TAC[LESS_OR_EQ;NOT_LESS_0]
      THEN DISCH_TAC THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC
      THEN REWRITE_TAC[LASTN;BUTLASTN;APPEND_NIL];
      DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[WORD_11]
      THEN MATCH_MP_TAC APPEND_BUTLASTN_LASTN THEN FIRST_ASSUM ACCEPT_TAC]);;

let WSPLIT_WCAT = TAC_PROOF(([],
  "!n m. !w1:(*)word::(PWORDLEN n). !w2:(*)word::(PWORDLEN m).
  (WSPLIT m(WCAT (w1,w2)) = (w1,w2))"),
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[WCAT_DEF]
    THEN PURE_REWRITE_TAC[WSPLIT_DEF;PAIR_EQ;WORD_11]
    THEN FIRST_ASSUM SUBST1_TAC THEN CONJ_TAC THENL[
      REWRITE_TAC[BUTLASTN_LENGTH_APPEND;APPEND_NIL];
      MATCH_ACCEPT_TAC LASTN_LENGTH_APPEND]);;

let WORD_PARTITION = save_thm(`WORD_PARTITION`,
    CONJ WCAT_WSPLIT WSPLIT_WCAT);;

let WCAT_ASSOC = prove_thm(`WCAT_ASSOC`,
    "!w1:(*)word. !w2:(*)word. !w3:(*)word.
    WCAT (w1,WCAT(w2,w3)) = WCAT(WCAT(w1,w2),w3)",
    REPEAT (word_INDUCT_TAC THEN GEN_TAC)
    THEN REWRITE_TAC[WCAT_DEF;APPEND_ASSOC]);;

let WCAT0 = prove_thm(`WCAT0`,
    "!w:(*)word. (WCAT(WORD[],w) = w) /\ (WCAT(w,WORD[]) = w)",
    word_INDUCT_TAC THEN PURE_REWRITE_TAC[WCAT_DEF;APPEND_NIL]
    THEN GEN_TAC THEN CONJ_TAC THEN REFL_TAC);;

let WCAT_11 = prove_thm(`WCAT_11`,
    "!m n. !wm1 wm2:(*)word::PWORDLEN m. !wn1 wn2:(*)word::PWORDLEN n.
     (WCAT (wm1,wn1) = WCAT (wm2,wn2)) = ((wm1 = wm2) /\ (wn1 = wn2))",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[WORD_11]
    THEN COND_REWRITE1_TAC APPEND_LENGTH_EQ
    THEN ASSUM_LIST (SUBST_TAC o (map SYM)) THEN REFL_TAC);;

let WSPLIT_PWORDLEN = prove_thm(`WSPLIT_PWORDLEN`,
    "!n. !w:(*)word::PWORDLEN n. !m. (m <= n) ==>
     (PWORDLEN (n - m) (FST(WSPLIT m w)) /\ PWORDLEN m (SND(WSPLIT m w)))",
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[WSPLIT_DEF;FST;SND;PWORDLEN_DEF]
    THEN REPEAT STRIP_TAC THENL
     map (\th. COND_REWRITE1_TAC th THENL[
       FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
       ASM_REWRITE_TAC[]]) [LENGTH_BUTLASTN; LENGTH_LASTN]);;

let WCAT_PWORDLEN = prove_thm(`WCAT_PWORDLEN`,
    "!n1. !w1:(*)word::PWORDLEN n1. !n2. !w2:(*)word::PWORDLEN n2.
     PWORDLEN (n1 + n2) (WCAT (w1,w2))",
    REPEAT (GEN_TAC THEN RESQ_WORDLEN_TAC)
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WCAT_DEF]
    THEN ASSUM_LIST SUBST_TAC
    THEN MATCH_ACCEPT_TAC (GSYM LENGTH_APPEND));;

let WORDLEN_SUC_WCAT = prove_thm(`WORDLEN_SUC_WCAT`,
    "!n (w:(*)word). PWORDLEN (SUC n) w ==> 
    (?b:(*)word::PWORDLEN 1. ?w':(*)word::PWORDLEN n. w = WCAT(b,w'))",
    let lem1 = SYM(REWRITE_RULE[LESS_REFL;SUB_EQUAL_0;SYM(num_CONV "1")]
      (SPECL["n:num";"n:num"](CONJUNCT2 SUB))) in
    REPEAT STRIP_TAC THEN RESQ_IMP_RES_TAC WSPLIT_PWORDLEN
    THEN RESQ_EXISTS_TAC "FST(WSPLIT n (w:(*)word))" THEN CONJ_TAC THENL[
      SUBST1_TAC lem1 THEN FIRST_ASSUM MATCH_MP_TAC
      THEN MATCH_ACCEPT_TAC LESS_EQ_SUC_REFL;
      RESQ_EXISTS_TAC "SND(WSPLIT n (w:(*)word))" THEN CONJ_TAC THENL[
    	FIRST_ASSUM MATCH_MP_TAC
    	THEN MATCH_ACCEPT_TAC LESS_EQ_SUC_REFL;
    	PURE_ONCE_REWRITE_TAC[PAIR]
    	THEN RESQ_IMP_RES_THEN (\t. SUBST1_TAC (MATCH_MP t
    	  (SPEC "n:num" LESS_EQ_SUC_REFL))) (CONJUNCT1 WORD_PARTITION)
    	THEN REFL_TAC]]);;

let WSEG_WSEG = prove_thm(`WSEG_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !m1 k1 m2 k2.
     ((m1 + k1) <= n) /\ ((m2 + k2) <= m1) ==>
     (WSEG m2 k2 (WSEG m1 k1 w) = WSEG m2 (k1 + k2) w)",
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[PWORDLEN_DEF;WSEG_DEF;WORD_11]
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN COND_REWRITE1_TAC BUTLASTN_LASTN THENL[
      COND_REWRITE1_TAC LENGTH_BUTLASTN
      THEN FIRST_ASSUM (SUBST1_TAC o SYM) THENL[
        IMP_RES_TAC LESS_EQ_SPLIT;
        COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
        THEN FIRST_ASSUM ACCEPT_TAC];
      COND_REWRITE1_TAC BUTLASTN_BUTLASTN THENL[
    	FIRST_ASSUM (SUBST1_TAC o SYM)
        THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC ADD_LESS_EQ_TRANS
        THEN EXISTS_TAC "m1:num" THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    	THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        COND_REWRITE1_TAC LASTN_LASTN THENL[
    	  COND_REWRITE1_TAC LENGTH_BUTLASTN
    	  THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
    	  THEN FIRST_ASSUM (SUBST_ALL_TAC o SYM)
    	  THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
    	  THEN COND_REWRITE1_TAC SUB_ADD 
    	  THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    	  COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB) THEN FIRST_ASSUM ACCEPT_TAC;
          CONV_TAC ((RAND_CONV o ONCE_DEPTH_CONV) (REWR_CONV ADD_SYM))
          THEN REFL_TAC]]]);;

let WSPLIT_WSEG = prove_thm(`WSPLIT_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !k. (k <= n) ==>
     (WSPLIT k w = (WSEG (n - k) k w), (WSEG k 0 w))",
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[WSPLIT_DEF;WSEG_DEF]
    THEN FIRST_ASSUM SUBST1_TAC
    THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[PAIR_EQ;WORD_11]
    THEN IMP_RES_THEN (SUBST1_TAC o SYM) LENGTH_BUTLASTN
    THEN PURE_REWRITE_TAC[BUTLASTN;LASTN_LENGTH_ID]
    THEN CONJ_TAC THEN REFL_TAC);;

let WSPLIT_WSEG1 = prove_thm(`WSPLIT_WSEG1`,
    "!n. !w:(*)word::PWORDLEN n. !k. (k <= n) ==>
     (FST(WSPLIT k w) = (WSEG (n - k) k w))",
    GEN_TAC THEN RESQ_GEN_TAC THEN REPEAT STRIP_TAC
    THEN RESQ_IMP_RES_TAC WSPLIT_WSEG
    THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let WSPLIT_WSEG2 = prove_thm(`WSPLIT_WSEG2`,
    "!n. !w:(*)word::PWORDLEN n. !k. (k <= n) ==>
     (SND(WSPLIT k w) = (WSEG k 0 w))",
    GEN_TAC THEN RESQ_GEN_TAC THEN REPEAT STRIP_TAC
    THEN RESQ_IMP_RES_TAC WSPLIT_WSEG
    THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let WCAT_WSEG_WSEG = prove_thm(`WCAT_WSEG_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !m1 m2 k. ((m1 + m2 + k) <= n) ==>
     (WCAT ((WSEG m2 (m1 + k) w), (WSEG m1 k w)) = WSEG (m1 + m2) k w)",
    GEN_TAC THEN RESQ_WORDLEN_TAC 
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN REPEAT STRIP_TAC 
    THEN COND_REWRITE1_TAC (GSYM BUTLASTN_BUTLASTN) THENL[
     POP_ASSUM MP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) 
     THEN CONV_TAC ARITH_CONV;
     MATCH_MP_TAC APPEND_LASTN_LASTN
     THEN COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
       IMP_RES_TAC LESS_EQ_SPLIT;
       FIRST_ASSUM SUBST_ALL_TAC THEN COND_REWRITE1_TAC(GSYM ADD_LESS_EQ_SUB)
       THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
       THEN FIRST_ASSUM ACCEPT_TAC]]);;

let WORD_SPLIT = save_thm(`WORD_SPLIT`,
    %"!n1 n2. !w:* word::PWORDLEN (n1 + n2).
      (w = WCAT ((WSEG n1 n2 w), (WSEG n2 0 w)))" %
    GEN_ALL (PURE_ONCE_REWRITE_RULE[ADD_SYM](RESQ_GEN_ALL (SYM (TRANS    
    (REWRITE_RULE[ADD_0;LESS_EQ_REFL] 
     (SPECL ["n2:num"; "n1:num"; "0"] 
      (RESQ_SPEC_ALL (SPEC "n2 + n1" WCAT_WSEG_WSEG))))
    (RESQ_SPEC_ALL (SPEC "n2 + n1" WSEG_WORD_LENGTH)) )))) );;

let WORDLEN_SUC_WCAT_WSEG_WSEG = save_thm(`WORDLEN_SUC_WCAT_WSEG_WSEG`,
%    "!n. !w:(*)word::PWORDLEN (SUC n).
    (w = WCAT((WSEG 1 n w),(WSEG n 0 w)))", %
    SUBS[SYM(PURE_ONCE_REWRITE_RULE[ADD_SYM](SPEC"n:num"ADD1))]
     (SPECL["1";"n:num"]WORD_SPLIT));;

let WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT =
    save_thm(`WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT`,
%    "!n. !w:(*)word::PWORDLEN (SUC n).
    (w = WCAT((WSEG n 1 w),(WSEG 1 0 w)))",%
    SUBS[SYM(SPEC"n:num"ADD1)] (SPECL["n:num";"1"]WORD_SPLIT));;

let WORDLEN_SUC_WCAT_BIT_WSEG = prove_thm(`WORDLEN_SUC_WCAT_BIT_WSEG`,
    "!n. !w:(*)word::PWORDLEN (SUC n).
    (w = WCAT(WORD[BIT n w],(WSEG n 0 w)))",
    GEN_TAC THEN RESQ_GEN_TAC THEN RESQ_REWRITE1_TAC(GSYM WSEG_BIT) THENL[
      MATCH_ACCEPT_TAC LESS_SUC_REFL;
      RESQ_IMP_RES_TAC WORDLEN_SUC_WCAT_WSEG_WSEG]);;

let WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT =
    prove_thm(`WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT`,
    "!n. !w:(*)word::PWORDLEN (SUC n).
    (w = WCAT((WSEG n 1 w),WORD[BIT 0 w]))",
    GEN_TAC THEN RESQ_GEN_TAC
    THEN RESQ_IMP_RES_THEN (\t. SUBST1_TAC (SYM(MATCH_MP t
      (SPEC "n:num" LESS_0)))) WSEG_BIT
    THEN RESQ_IMP_RES_TAC WORDLEN_SUC_WCAT_WSEG_WSEG_RIGHT);;

let WSEG_WCAT1 = prove_thm(`WSEG_WCAT1`,
    "!n1 n2. !w1:* word::PWORDLEN n1. !w2:* word::PWORDLEN n2.
     WSEG n1 n2 (WCAT(w1,w2)) = w1",
    REPEAT GEN_TAC THEN MAP_EVERY
      (\w. RESQ_HALF_GEN_TAC THEN GEN_TAC THEN word_CASES_TAC w THEN DISCH_TAC)
    	    ["w1:* word"; "w2:* word"]
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN SUBST_TAC (map ((MATCH_EQ_MP PWORDLEN_DEF) o ASSUME )
    	["PWORDLEN n1 (WORD (l:* list))";"PWORDLEN n2 (WORD (l':* list))"])
    THEN REWRITE_TAC[BUTLASTN_LENGTH_APPEND;APPEND_NIL;LASTN_LENGTH_ID]);;

let WSEG_WCAT2 = prove_thm(`WSEG_WCAT2`,
    "!n1 n2. !w1:* word::PWORDLEN n1. !w2:* word::PWORDLEN n2.
     WSEG n2 0 (WCAT(w1,w2)) = w2",
    REPEAT GEN_TAC THEN MAP_EVERY
     (\w. RESQ_HALF_GEN_TAC THEN GEN_TAC THEN word_CASES_TAC w THEN DISCH_TAC)
    	    ["w1:* word"; "w2:* word"]
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN SUBST1_TAC (MATCH_EQ_MP PWORDLEN_DEF
    	    (ASSUME "PWORDLEN n2 (WORD (l':* list))"))
    THEN REWRITE_TAC[LASTN_LENGTH_APPEND;BUTLASTN]);;


% |- !n.
    !w :: PWORDLEN n.
     !k m1.
      (k + (SUC m1)) < n ==>
      (WSEG(SUC m1)k w = WCAT(WSEG 1(k + m1)w,WSEG m1 k w)) %
%<
let WSEG_SUC =  GEN_ALL
    (RESQ_GEN ("w:(*)word","PWORDLEN n:(*)word->bool")(GENL["k:num";"m1:num"]
    (CONV_RULE (RAND_CONV SYM_CONV) (SUBS[SYM(SPEC"m1:num"ADD1)]
    (SPECL["k:num";"m1:num";"1"](RESQ_SPEC"w:(*)word"
    (SPEC_ALL WCAT_WSEG_WSEG)))))));;
>%

% |- !k l. WSEG 0 k(WORD l) = WORD[] %
%< let WSEG0 = PURE_REWRITE_RULE[LASTN](SPEC"0"WSEG_DEF);; >%

let WORD_CONS_WCAT = prove_thm(`WORD_CONS_WCAT`,
    "!(x:*) l. WORD(CONS x l) = WCAT ((WORD [x]), (WORD l))",
    REPEAT GEN_TAC THEN REWRITE_TAC[WCAT_DEF]
    THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC CONS_APPEND);;

let WORD_SNOC_WCAT = prove_thm(`WORD_SNOC_WCAT`,
    "!(x:*) l. WORD(SNOC x l) = WCAT ((WORD l), (WORD [x]))",
    REPEAT GEN_TAC THEN REWRITE_TAC[WCAT_DEF]
    THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC SNOC_APPEND);;

let BIT_WCAT_FST = prove_thm(`BIT_WCAT_FST`,
    "!n1 n2. !w1:* word::PWORDLEN n1. !w2:* word::PWORDLEN n2.
     !k. n2 <= k /\ k < (n1 + n2) ==>
     (BIT k (WCAT (w1,w2)) = BIT (k - n2) w1)",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[BIT_DEF]
    THEN COND_REWRITE1_TAC ELL_APPEND1
    THEN FIRST_ASSUM (SUBST1_TAC o SYM) THENL[
      FIRST_ASSUM ACCEPT_TAC;
      REFL_TAC]);;

let BIT_WCAT_SND = prove_thm(`BIT_WCAT_SND`,
    "!n1 n2. !w1:* word::PWORDLEN n1. !w2:* word::PWORDLEN n2.
     !k. k < n2 ==> (BIT k (WCAT (w1,w2)) = BIT k w2)",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[BIT_DEF]
    THEN COND_REWRITE1_TAC ELL_APPEND2
    THEN FIRST_ASSUM (SUBST1_TAC o SYM) THENL[
      FIRST_ASSUM ACCEPT_TAC; REFL_TAC]);;

let BIT_WCAT1 = prove_thm(`BIT_WCAT1`,
    "!n. !w:(*)word::PWORDLEN n. !b. BIT n (WCAT (WORD[b], w)) = b",
    INDUCT_TAC THENL[
      RESQ_HALF_GEN_TAC THEN GEN_TAC
      THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP PWORDLEN0))
      THEN REWRITE_TAC[WCAT0;BIT0];
      RESQ_HALF_GEN_TAC THEN GEN_TAC THEN word_CASES_TAC "w:(*)word"
      THEN PURE_REWRITE_TAC[WCAT_DEF;BIT_DEF;APPEND;PWORDLEN_DEF]
      THEN DISCH_THEN SUBST1_TAC
      THEN MATCH_ACCEPT_TAC ELL_LENGTH_CONS]);;

let WSEG_WCAT_WSEG1 = prove_thm(`WSEG_WCAT_WSEG1`,
    "!n1 n2. !w1:(*)word::PWORDLEN n1. !w2:(*)word::PWORDLEN n2.
     !m k. (m <= n1) /\ (n2 <= k) ==>
    (WSEG m k (WCAT (w1, w2)) = WSEG m (k - n2) w1)",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN COND_REWRITE1_TAC BUTLASTN_APPEND1 THENL[
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[]]);;

let WSEG_WCAT_WSEG2 = prove_thm(`WSEG_WCAT_WSEG2`,
    "!n1 n2. !w1:(*)word::PWORDLEN n1. !w2:(*)word::PWORDLEN n2.
     !m k. (m + k) <= n2 ==> (WSEG m k (WCAT (w1, w2)) = WSEG m k w2)",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN COND_REWRITE1_TAC BUTLASTN_APPEND2 THENL[
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT;
      COND_REWRITE1_TAC LASTN_APPEND2 THEN TRY REFL_TAC
      THEN COND_REWRITE1_TAC LENGTH_BUTLASTN
      THEN FIRST_ASSUM (SUBST1_TAC o SYM)
      THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB) THENL[
        IMP_RES_TAC LESS_EQ_SPLIT;
    	FIRST_ASSUM ACCEPT_TAC]]);;

let WSEG_WCAT_WSEG = prove_thm(`WSEG_WCAT_WSEG`,
  "!n1 n2. !w1:(*)word::PWORDLEN n1. !w2:(*)word::PWORDLEN n2.
   !m k. (m + k) <= (n1 + n2) /\ (k < n2) /\ (n2 <= (m + k)) ==> 
  (WSEG m k (WCAT(w1,w2)) = 
    WCAT((WSEG((m + k) - n2) 0 w1),(WSEG (n2 -k) k w2)))",
    REPEAT GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[WCAT_DEF;WSEG_DEF;WORD_11]
    THEN PURE_ONCE_ASM_REWRITE_TAC[BUTLASTN]
    THEN PURE_ONCE_ASM_REWRITE_TAC[WORD_11]
    THEN COND_REWRITE1_TAC LASTN_BUTLASTN_APPEND
    THEN (REFL_TAC ORELSE    
      RULE_ASSUM_TAC (\t. SYM t ? t) THEN ASM_REWRITE_TAC[]));;

let PWORDLEN_BIT1 = % |- !x. PWORDLEN 1(WORD[x]) %
    GEN_ALL (REWRITE_RULE[LENGTH;SYM(num_CONV "1")]
    (SPECL ["1"; "[x:*]"] PWORDLEN_DEF));;

let BIT_EQ_IMP_WORD_EQ = prove_thm(`BIT_EQ_IMP_WORD_EQ`,
    "!n. !w1 w2:(*)word::PWORDLEN n.
     (!k. k < n ==> (BIT k w1 = BIT k w2)) ==> (w1 = w2)",
    let lm =  (SPEC "n:num" WORDLEN_SUC_WCAT_BIT_WSEG) in
    let seg_lm = ((GEN "w:* word") o DISCH_ALL)
    	(REWRITE_RULE[ADD_0;LESS_EQ_SUC_REFL]
    	(SPECL ["n:num"; "0"] (RESQ_SPEC_ALL (SPEC "SUC n" WSEG_PWORDLEN)))) in
    let lms1 = (map (\t.UNDISCH_ALL(SPEC t seg_lm))
    	["w2:* word";"w1:* word"]) in
    let asm1 = ASSUME "!w1 w2 :* word :: PWORDLEN n.
        (!k. k < n ==> (BIT k w1 = BIT k w2)) ==> (w1 = w2)" in
    let lem2 = itlist (\t1 t2. RESQ_MATCH_MP t2 t1) lms1 asm1 in
    let wcat_lem = GEN_ALL (itlist (\t1 t2. RESQ_MATCH_MP t2 t1)
    	 (lms1 @ (map (\t. SPEC t PWORDLEN_BIT1)
    	    ["BIT n (w2:* word)";"BIT n (w1:* word)"])) 
    	 (SPECL ["1"; "n:num"] WCAT_11)) in
    let bit_seg =
    	let lm = RESQ_GEN_ALL (REWRITE_RULE[ADD_CLAUSES;LESS_EQ_SUC_REFL]
    	     (SPECL ["n:num"; "0"; "k:num"]
    	      (RESQ_SPEC_ALL (SPEC "SUC n" BIT_WSEG)))) in
    	(map (\t. UNDISCH_ALL(RESQ_SPEC t lm)) ["w1:* word";"w2:* word"]) in
    INDUCT_TAC THEN REPEAT RESQ_GEN_TAC THENL[
     ASSUM_LIST (\asl. MAP_EVERY SUBST1_TAC (map (MATCH_MP PWORDLEN0) asl))
     THEN DISCH_TAC THEN REFL_TAC;
     DISCH_TAC THEN RESQ_IMP_RES_TAC WORDLEN_SUC_WCAT_BIT_WSEG
     THEN PURE_ONCE_ASM_REWRITE_TAC[]
     THEN PURE_ONCE_REWRITE_TAC[wcat_lem] THEN CONJ_TAC THENL[
      PURE_REWRITE_TAC[WORD_11;CONS_11]
      THEN ASSUME_TAC (SPEC "n:num" LESS_SUC_REFL)
      THEN RES_THEN (\t.REWRITE_TAC[t]);
      MATCH_MP_TAC lem2 THEN REPEAT STRIP_TAC
      THEN SUBST_TAC bit_seg THEN FIRST_ASSUM MATCH_MP_TAC
      THEN IMP_RES_TAC LESS_SUC]]);;

close_theory();;
