% ===================================================================== %
% FILE: mk_word_bitop.ml	    DATE: 14 Aug 1992			%
% AUTHOR: Wai WONG  	    	    					%
% Writes: word_bitop.th	    	    					%
% Uses: Libraries: arith res_quan					%
% Description: Creates a theorey for generic word bitwise operations	%
% ===================================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

loadt(`ver_`^(string_of_int(version())));;
loadf`arith_thms`;;

load_theory`word_base`;;
autoload_all`word_base`;;

new_theory`word_bitop`;;

loadf`word_funs`;;

% --------------------------------------------------------------------- %
% We begin with some lemmas about lists. They are used in the proofs.	%
% --------------------------------------------------------------------- %
let LASTN_BUTLASTN_SEG = PROVE(
    "!m k (l:* list). (m + k) <= (LENGTH l) ==>
     (LASTN m (BUTLASTN k l) = SEG m((LENGTH l) - (m + k))l)",
    let lem1 = ARITH_PROVE
    	 "!l m k. (m+k)<=l ==>((m + (l - (m + k))) = (l - k))" in
    let lem2 = ARITH_PROVE
    	 "!l m k. (m+k)<=l ==> ((l - (m + (l - (m + k)))) = k)" in
    REPEAT STRIP_TAC THEN COND_REWRITE1_TAC SEG_LASTN_BUTLASTN THENL[
        IMP_RES_THEN (\t.REWRITE_TAC[t])lem1
    	THEN MATCH_ACCEPT_TAC SUB_LESS_EQ;
        IMP_RES_THEN (\t.REWRITE_TAC[t])lem2]);;

%---------------------------------------------------------------%
% Bitwise operators 	    	    				%
%---------------------------------------------------------------%

%---------------------------------------------------------------%
% PBITOP (op:* word -> ** word) is true if op is a bitwise	%
% unary operator    	    	    				%
%---------------------------------------------------------------%

let PBITOP_DEF = new_definition(`PBITOP_DEF`,
    "PBITOP (op:* word -> ** word) =
     !n. !w:* word ::PWORDLEN n. PWORDLEN n (op w) /\
     !m k. ((m + k) <= n) ==> (op(WSEG m k w) = WSEG m k (op w))");;

let PBITOP_PWORDLEN = prove_thm(`PBITOP_PWORDLEN`,
    "!op:(*)word->(**)word::PBITOP. !n. !w:(*)word::PWORDLEN n.
     (PWORDLEN n (op w))",
    REPEAT GGEN_TAC THEN IMP_RES_TAC PBITOP_DEF THEN RESQ_RES_TAC);;

let PBITOP_WSEG = prove_thm(`PBITOP_WSEG`,
    "!op:(*)word->(**)word::PBITOP. !n. !w:(*)word::PWORDLEN n.
     !m k. ((m + k) <= n) ==> (op(WSEG m k w) = WSEG m k (op w))",
    RESQ_GEN_TAC THEN GEN_TAC THEN RESQ_GEN_TAC
    THEN IMP_RES_TAC PBITOP_DEF THEN RESQ_RES_TAC);;

let PBITOP_BIT = prove_thm(`PBITOP_BIT`,
    "!op:(*)word->(**)word::PBITOP.
     !n. !w:* word ::PWORDLEN n. !k. (k < n) ==>
     (op(WORD[BIT k w]) = WORD[BIT k (op w)])",
    RESQ_HALF_GEN_TAC THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[PBITOP_DEF]
    THEN DISCH_TAC THEN GEN_TAC THEN RESQ_GEN_TAC
    THEN REPEAT STRIP_TAC THEN RESQ_RES_TAC
    THEN RESQ_IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) WSEG_BIT)
    THEN RES_TAC THEN POP_ASSUM SUBST1_TAC THEN POP_ASSUM SUBST1_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN PURE_REWRITE_TAC[ADD] THEN IMP_RES_TAC LESS_EQ);;

let BIT_op_EXISTS = PROVE(
    "!op:(*)word->(**)word::PBITOP. ?op':*->**. !n. !w:(*)word::PWORDLEN n.
     !k. (k < n) ==> ((BIT k (op w)) = (op'(BIT k w)))",
    RESQ_GEN_TAC THEN EXISTS_TAC"\b:*.BIT 0((op:(*)word->(**)word)(WORD[b]))"
    THEN GEN_TAC THEN RESQ_HALF_GEN_TAC THEN GEN_TAC THEN REPEAT STRIP_TAC
    THEN RESQ_IMP_RES_TAC PBITOP_BIT THEN RES_THEN SUBST1_TAC
    THEN REWRITE_TAC[BIT0]);;

%---------------------------------------------------------------%
% PBITBOP (op:* word -> ** word -> *** word) is true if op is a %
%  bitwise binary operator  	    				%
%---------------------------------------------------------------%

let PBITBOP_DEF = new_definition(`PBITBOP_DEF`,
    "PBITBOP (op:* word  -> ** word -> *** word) =
     !n. !w1:* word ::PWORDLEN n. !w2:** word ::PWORDLEN n.
     (PWORDLEN n (op w1 w2)) /\
     !m k. ((m + k) <= n) ==>
     (op (WSEG m k w1) (WSEG m k w2) = WSEG m k (op w1 w2))");;

let PBITBOP_PWORDLEN = prove_thm(`PBITBOP_PWORDLEN`,
    "!op:* word  -> ** word -> *** word::PBITBOP.
     !n. !w1:* word ::PWORDLEN n. !w2:** word ::PWORDLEN n.
     (PWORDLEN n (op w1 w2))",
    REPEAT GGEN_TAC THEN IMP_RES_TAC PBITBOP_DEF THEN RESQ_RES_TAC);;

let PBITBOP_WSEG = prove_thm(`PBITBOP_WSEG`,
    "!op:* word  -> ** word -> *** word::PBITBOP.
     !n. !w1:* word ::PWORDLEN n. !w2:** word ::PWORDLEN n.
     !m k. ((m + k) <= n) ==> 
     (op (WSEG m k w1) (WSEG m k w2) = WSEG m k (op w1 w2))",
    RESQ_GEN_TAC THEN GEN_TAC THEN  REPEAT RESQ_GEN_TAC
    THEN IMP_RES_TAC PBITBOP_DEF THEN RESQ_RES_TAC);;

let PBITBOP_EXISTS = prove_thm(`PBITBOP_EXISTS`,
    "!f:*->**->***. ?fn. !l1 l2. fn (WORD l1)(WORD l2) = WORD(MAP2 f l1 l2)",
    let th = prove_rec_fn_exists word_Ax "bt (WORD l) = (l:* list)" in
    GEN_TAC THEN CHOOSE_TAC (INST_TYPE [":**",":*"] th)
    THEN CHOOSE_TAC th THEN EXISTS_TAC
      "\(w1:(*)word) (w2:(**)word). WORD(MAP2 (f:*->**->***) (bt' w1) (bt w2))"
    THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]);;

%---------------------------------------------------------------%
% WMAP: applies a function to every bit of a word		%
% WMAP: (*->**) -> * word -> ** word				%
%---------------------------------------------------------------%

let WMAP_DEF = new_recursive_definition false word_Ax `WMAP_DEF`
    "!f:*->**. !l. WMAP f (WORD l) = WORD (MAP f l)";;

let WMAP_PWORDLEN = prove_thm(`WMAP_PWORDLEN`,
    "!w::PWORDLEN n. !f:*->**. PWORDLEN n (WMAP f w)",
    RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WMAP_DEF;PWORDLEN_DEF;LENGTH_MAP]);;

let WMAP0 = prove_thm(`WMAP_0`,
    "!f:*->**. (WMAP f (WORD[]:* word) = WORD []:** word)",
    REWRITE_TAC[WMAP_DEF;MAP]);;

let WMAP_BIT = prove_thm(`WMAP_BIT`,
    "!n. !w:* word ::PWORDLEN n. !k. k < n ==>
     !f:*->**. BIT k (WMAP f w) = f (BIT k w)",
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[BIT_DEF;WMAP_DEF]
    THEN MATCH_MP_TAC ELL_MAP THEN FIRST_ASSUM (SUBST1_TAC o SYM)
    THEN FIRST_ASSUM ACCEPT_TAC);;

let WMAP_WSEG = prove_thm(`WMAP_WSEG`,
    "!n. !w :: PWORDLEN n.
     !m k. (m + k) <= n ==>
     !f:*->**. (WMAP f(WSEG m k w) = WSEG m k(WMAP f w))",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WMAP_DEF;WSEG_DEF;PWORDLEN_DEF;WORD_11]
    THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC
    THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP THENL[
     IMP_RES_TAC LESS_EQ_SPLIT;
     COND_REWRITE1_TAC LASTN_MAP THENL[
      COND_REWRITE1_TAC LENGTH_BUTLASTN 
      THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
      THEN FIRST_ASSUM ACCEPT_TAC;
      REFL_TAC]]);;

let WMAP_PBITOP = prove_thm(`WMAP_PBITOP`,
    "!f:*->**. PBITOP (WMAP f)",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[PBITOP_DEF]
    THEN GEN_TAC THEN RESQ_GEN_TAC THEN CONJ_TAC THENL[
     RESQ_IMP_RES_THEN MATCH_ACCEPT_TAC WMAP_PWORDLEN;
     REPEAT STRIP_TAC THEN RESQ_IMP_RES_TAC WMAP_WSEG
     THEN RES_THEN MATCH_ACCEPT_TAC]);;

let WMAP_WCAT = prove_thm(`WMAP_WCAT`,
    "!w1 w2 (f:*->**).
     WMAP f(WCAT (w1,w2)) = WCAT ((WMAP f w1), (WMAP f w2))",
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[WCAT_DEF;WMAP_DEF;MAP_APPEND]);;

let WMAP_o = prove_thm(`WMAP_o`,
    "!w. !f:*->**. !g:**->***. WMAP g (WMAP f w) = WMAP (g o f) w",
    word_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[WMAP_DEF;MAP_MAP_o]);;

%---------------------------------------------------------------%
% FORALLBITS : (* -> bool) -> (*)word -> bool			%
%---------------------------------------------------------------%

let FORALLBITS_DEF = new_recursive_definition false word_Ax `FORALLBITS_DEF`
    "!P:*->bool. !l. FORALLBITS P (WORD l) = ALL_EL P l";;

let FORALLBITS = prove_thm(`FORALLBITS`,
    "!n. !w:(*)word::PWORDLEN n. !P.
     FORALLBITS P w = (!k. k < n ==> P(BIT k w))",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PWORDLEN_DEF;FORALLBITS_DEF;BIT_DEF]
    THEN MAP_EVERY SPEC_TAC [("n:num","n:num");("l:* list","l:* list")]
    THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH;ALL_EL]
    THEN DISCH_THEN SUBST1_TAC THENL[
      REWRITE_TAC[NOT_LESS_0];
      GEN_TAC THEN EQ_TAC THEN PURE_ONCE_REWRITE_TAC[LESS_THM] THENL[
    	STRIP_TAC THEN GEN_TAC 
    	THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
    	  ASM_REWRITE_TAC[ELL_LENGTH_CONS];
    	  IMP_RES_THEN (\t. REWRITE_TAC[t]) ELL_CONS
    	  THEN FIRST_ASSUM (SUBST_ALL_TAC o SPEC_ALL o (REWRITE_RULE[]) o
    	    (SPEC"LENGTH (l:* list)")) THEN RES_TAC];
      DISCH_TAC THEN CONJ_TAC THEN POP_ASSUM MP_TAC
      THEN FIRST_ASSUM (SUBST_ALL_TAC o SPEC_ALL o (REWRITE_RULE[]) o
    	    (SPEC"LENGTH (l:* list)")) THENL[
        CONV_TAC LEFT_IMP_FORALL_CONV
        THEN EXISTS_TAC"LENGTH (l:* list)"
        THEN REWRITE_TAC[LESS_REFL;ELL_LENGTH_CONS];
    	REPEAT STRIP_TAC THEN RES_THEN MP_TAC
        THEN IMP_RES_THEN (\t.REWRITE_TAC[t]) ELL_CONS]]]);;

let FORALLBITS_WSEG = prove_thm(`FORALLBITS_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !P.
     FORALLBITS P w ==> 
     !m k. (m + k) <= n ==> FORALLBITS P (WSEG m k w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WSEG_DEF;PWORDLEN_DEF;FORALLBITS_DEF]
    THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC
    THEN SPEC_TAC("l:* list","l:* list") THEN SNOC_INDUCT_TAC THENL[
     REWRITE_TAC[LENGTH;ALL_EL] THEN REPEAT STRIP_TAC
     THEN IMP_RES_THEN (SUBST_TAC o CONJUNCTS o
    	 (PURE_ONCE_REWRITE_RULE[ADD_EQ_0])) LESS_EQ_0_EQ
     THEN REWRITE_TAC[LASTN;BUTLASTN;ALL_EL];
     REWRITE_TAC[LENGTH_SNOC;ALL_EL_SNOC]
     THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[LASTN;ALL_EL];
      INDUCT_TAC THENL[
       REWRITE_TAC[BUTLASTN;ADD_CLAUSES;LASTN;ALL_EL_SNOC;LESS_EQ_MONO]
       THEN DISCH_TAC THEN IMP_RES_TAC ALL_EL_LASTN
       THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
       REWRITE_TAC[BUTLASTN;LESS_EQ_MONO;GEN_ALL(el 4(CONJUNCTS ADD_CLAUSES))]
       THEN DISCH_TAC THEN RES_TAC]]]);;

let FORALLBITS_WCAT = prove_thm(`FORALLBITS_WCAT`,
    "!w1 w2:(*)word.  !P.
     FORALLBITS P (WCAT(w1,w2)) = (FORALLBITS P w1 /\ FORALLBITS P w2)",
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[FORALLBITS_DEF;WCAT_DEF;ALL_EL_APPEND]);;

%---------------------------------------------------------------%
% EXISTSABIT : (* -> bool) -> (*)word -> bool			%
%---------------------------------------------------------------%

let EXISTSABIT_DEF = new_recursive_definition false word_Ax `EXISTSABIT_DEF`
    "!P:*->bool. !l. EXISTSABIT P (WORD l) = SOME_EL P l";;

let NOT_EXISTSABIT = prove_thm(`NOT_EXISTSABIT`,
    "!P:*->bool. !w:(*)word.
     ~(EXISTSABIT P w) = (FORALLBITS ($~ o P) w)",
    GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF;FORALLBITS_DEF;NOT_SOME_EL_ALL_EL]);;

let NOT_FORALLBITS = prove_thm(`NOT_FORALLBITS`,
    "!P:*->bool. !w:(*)word.
     ~(FORALLBITS P w) = (EXISTSABIT ($~ o P) w)",
    GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF;FORALLBITS_DEF;NOT_ALL_EL_SOME_EL]);;

let EXISTSABIT_BIT = prove_thm(`EXISTSABIT`,
    "!n. !w:(*)word::PWORDLEN n. !P.
     EXISTSABIT P w = ?k. k < n /\ P(BIT k w)",
    GEN_TAC THEN RESQ_HALF_GEN_TAC THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PWORDLEN_DEF;EXISTSABIT_DEF;BIT_DEF]
    THEN DISCH_THEN SUBST1_TAC 
    THEN MAP_EVERY SPEC_TAC [("n:num","n:num");("l:* list","l:* list")]
    THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH;SOME_EL;NOT_LESS_0]
    THEN PURE_ONCE_REWRITE_TAC[LESS_THM] THEN EQ_TAC THENL[
      STRIP_TAC THENL[
    	EXISTS_TAC "LENGTH(l:* list)" THEN ASM_REWRITE_TAC[ELL_LENGTH_CONS];
    	RES_TAC THEN EXISTS_TAC "k:num"
        THEN COND_REWRITE1_TAC ELL_CONS THEN ASM_REWRITE_TAC[]];
      PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
      THEN DISCH_THEN (STRIP_THM_THEN 
    	(DISJ_CASES_THEN2 STRIP_ASSUME_TAC MP_TAC)) THENL[
    	FIRST_ASSUM SUBST_ALL_TAC
        THEN RULE_ASSUM_TAC (REWRITE_RULE[ELL_LENGTH_CONS])
    	THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    	DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
    	THEN COND_REWRITE1_TAC ELL_CONS THEN DISCH_TAC THEN RES_TAC
    	THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let EXISTSABIT_WSEG = prove_thm(`EXISTSABIT_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !m k. ((m + k) <= n) ==>
     !P. (EXISTSABIT P (WSEG m k w)) ==> (EXISTSABIT P w)",
    let lem1 = ARITH_PROVE
    	 "!l m k. (m+k)<=l ==>((m + (l - (m + k))) = (l - k))" in
    GEN_TAC THEN RESQ_HALF_GEN_TAC  THEN word_INDUCT_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF;PWORDLEN_DEF;WSEG_DEF]
    THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN COND_REWRITE1_TAC LASTN_BUTLASTN_SEG
    THEN MATCH_MP_TAC (SPECL
    	["m:num";"(LENGTH (l:* list)) - (m + k)";"l:* list"] SOME_EL_SEG)
    THEN IMP_RES_THEN SUBST1_TAC lem1
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);;

let EXISTSABIT_WCAT = prove_thm(`EXISTSABIT_WCAT`,
    "!w1 w2:(*)word.  !P.
     EXISTSABIT P (WCAT(w1,w2)) = (EXISTSABIT P w1 \/ EXISTSABIT P w2)",
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF;WCAT_DEF;SOME_EL_APPEND]);;


%---------------------------------------------------------------%
% Shift and rotation   	    					%
%---------------------------------------------------------------%

let SHR_DEF = new_definition(`SHR_DEF`,
    "SHR f b (w:(*)word) =
     WCAT((f => (WSEG 1 (PRE(WORDLEN w)) w) | WORD[b]),
           (WSEG (PRE(WORDLEN w)) 1 w)), (BIT 0 w)");;

let SHL_DEF = new_definition(`SHL_DEF`,
    "SHL f (w:(*)word) b = 
     (BIT (PRE(WORDLEN w)) w),
     WCAT((WSEG (PRE(WORDLEN w)) 0 w),(f => (WSEG 1 0 w) | WORD[b]))");;

% 6 Feb 94 %

let SHR_WSEG = prove_thm(`SHR_WSEG`,
    "!n. !w:(*)word::PWORDLEN n. !m k. ((m + k) <= n) ==> (0 < m) ==>
     (!f b. SHR f b (WSEG m k w) =
      (f => (WCAT((WSEG 1 (k+(m-1)) w),(WSEG (m-1)(k+1)w))) |
            (WCAT( (WORD[b]),       (WSEG (m-1)(k+1)w)))), (BIT k w))",
    let lem1 = ARITH_PROVE"0 < m ==> (((m-1)+1) <= m)" in
    GEN_TAC THEN RESQ_GEN_TAC THEN PURE_REWRITE_TAC[SHR_DEF]
    THEN REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
      BOOL_CASES_TAC "f:bool" THEN PURE_ONCE_REWRITE_TAC[COND_CLAUSES]
      THEN RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
      THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] 
      THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1] THEN CONJ_TAC THEN TRY REFL_TAC
      THEN MATCH_MP_TAC (RESQ_SPEC"w:* word"(SPEC"n:num" WSEG_WSEG))
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[]
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      RESQ_IMP_RES_TAC BIT_WSEG THEN RES_TAC THEN ASM_REWRITE_TAC[ADD]]);;    	

% |- !n. !w :: PWORDLEN n.
     !m k. (m + k) <= n ==> 0 < m ==>
      (!b. SHR F b(WSEG m k w) = WCAT(WORD[b],WSEG(m - 1)(k + 1)w),BIT k w) %
let SHR_WSEG_1F = save_thm(`SHR_WSEG_1F`,
    let th1 = SPEC_ALL(RESQ_SPEC_ALL(SPEC_ALL SHR_WSEG)) in
    let P,v = dest_comb(hd(hyp th1)) in
    let ante = fst(strip_imp(concl th1)) in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV COND_CONV)
    	(SPEC "F" (UNDISCH_ALL th1)) in
    GEN_ALL(RESQ_GEN (v,P) (GEN_ALL(itlist DISCH ante th2))));;

let SHR_WSEG_NF_lem1 = ARITH_PROVE "0 < m ==>((m-1)+1 = m)";;

let SHR_WSEG_NF_lem2 = ARITH_PROVE "0 < m ==>( (m-1) + (k+1) = m+k)";;

let SHR_WSEG_NF = prove_thm(`SHR_WSEG_NF`,
    "!n. !w :(*)word :: PWORDLEN n.
     !m k. (m + k) < n ==> 0 < m ==>
      (SHR F(BIT(m + k)w)(WSEG m k w) = (WSEG m (k + 1)w), (BIT k w))",
    REPEAT GGEN_TAC THEN REPEAT DISCH_TAC
    THEN RESQ_IMP_RES_TAC SHR_WSEG THEN POP_ASSUM
      (ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)))
    THEN FIRST_ASSUM COND_REWRITE1_TAC THENL[
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ;
      CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
      THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
        RESQ_IMP_RES_THEN COND_REWRITE1_TAC 
          (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)WSEG_BIT)
        THEN RESQ_IMP_RES_TAC WCAT_WSEG_WSEG
        THEN POP_ASSUM (MP_TAC o (SPECL ["m-1";"1";"k+1"]))
        THEN MAP_EVERY COND_REWRITE1_TAC [SHR_WSEG_NF_lem1;SHR_WSEG_NF_lem2]
        THEN DISCH_THEN MATCH_MP_TAC 
    	THEN PURE_REWRITE_TAC[GSYM ADD1;ADD_CLAUSES]
    	THEN SUBST1_TAC (SPECL["1";"k:num"]ADD_SYM)
    	THEN COND_REWRITE1_TAC SHR_WSEG_NF_lem2
    	THEN MATCH_MP_TAC LESS_OR THEN FIRST_ASSUM ACCEPT_TAC;
    	REFL_TAC]]);;

let SHL_WSEG = prove_thm(`SHL_WSEG`, 
    "!n. !w:(*)word::PWORDLEN n. !m k. ((m + k) <= n) ==> (0 < m) ==>
     (!f b. SHL f (WSEG m k w) b = ((BIT (k+m-1) w),
      (f => (WCAT((WSEG (m-1) k w),(WSEG 1 k w))) |
            (WCAT((WSEG (m-1) k w),(WORD[b])))))) ",
    let f t1 tms =
        ((IMP_RES_THEN SUBST1_TAC) o (\th. MATCH_MP th t1)
    	  o (PURE_ONCE_REWRITE_RULE[ADD_CLAUSES]) o (SPECL tms)) in
    REPEAT GGEN_TAC THEN PURE_REWRITE_TAC[SHL_DEF] THEN REPEAT DISCH_TAC
    THEN REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ]
    THEN CONJ_TAC THENL[
      RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
      THEN RESQ_IMP_RES_THEN (IMP_RES_THEN COND_REWRITE1_TAC) BIT_WSEG THENL[
    	IMP_RES_TAC PRE_LESS_REFL;
    	CONV_TAC ((RAND_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV ADD_SYM))
        THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1] THEN REFL_TAC];
      BOOL_CASES_TAC "f:bool" THEN CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
      THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC
      THEN TRY REFL_TAC THENL[
        RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
    	THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
    	THEN RESQ_REWRITE1_TAC WSEG_WSEG THENL[
    	  ARITH_TAC;
    	  REWRITE_TAC[ADD_0]];
    	RESQ_REWRITE1_TAC WSEG_WSEG THENL[
    	  ARITH_TAC;
    	  REWRITE_TAC[ADD_0]];
        RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
    	THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
    	THEN RESQ_REWRITE1_TAC WSEG_WSEG THENL[
    	  ARITH_TAC;
    	  REWRITE_TAC[ADD_0]]]]);;

% |- !n. !w :: PWORDLEN n.
     !m k. (m + k) <= n ==> 0 < m ==>
      (!b. SHL F(WSEG m k w)b = BIT(k + (m - 1))w,WCAT(WSEG(m - 1)k w,WORD[b])) %
let SHL_WSEG_1F = save_thm(`SHL_WSEG_1F`,
    let th1 = SPEC_ALL(RESQ_SPEC_ALL(SPEC_ALL SHL_WSEG)) in
    let P,v = dest_comb(hd(hyp th1)) in
    let ante = fst(strip_imp(concl th1)) in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV COND_CONV)
    	(SPEC "F" (UNDISCH_ALL th1)) in
    GEN_ALL(RESQ_GEN (v,P) (GEN_ALL(itlist DISCH ante th2))));;

let SHL_WSEG_NF = prove_thm(`SHL_WSEG_NF`,
    "!n. !w :(*)word :: PWORDLEN n.
     !m k. (m + k) <= n ==> 0 < m ==> (0 < k) ==>
      (SHL F (WSEG m k w)(BIT(k - 1)w) =
    	 (BIT (k + m - 1) w),(WSEG m (k - 1)w))",
    REPEAT GGEN_TAC THEN REPEAT DISCH_TAC THEN RESQ_REWRITE1_TAC SHL_WSEG
    THEN REWRITE_TAC[PAIR_EQ]
    THEN RESQ_REWRITE1_TAC (GSYM WSEG_BIT) THENL[
      ARITH_TAC;
      RESQ_IMP_RES_THEN (MP_TAC o (SPECL ["1";"m-1";"k-1"])) WCAT_WSEG_WSEG
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN COND_REWRITE1_TAC SUB_ADD 
      THEN TRY (CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN IMP_RES_TAC LESS_OR)
      THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC]);;

let WSEG_SHL = prove_thm(`WSEG_SHL`,
    "!n. !w:* word :: PWORDLEN (SUC n). !m k.
     0 < k /\ (m + k) <= (SUC n) ==>
     (!b. WSEG m k (SND (SHL f w b)) = WSEG m (k - 1) w)",
    REPEAT GGEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SHL_DEF] 
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_EQ_MP PWORDLEN))
    THEN REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN RESQ_REWRITE1_TAC (SPECL["n:num"; "1"] WSEG_WCAT_WSEG1) THENL[
      RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
      THEN REWRITE_TAC[ADD_0;LESS_EQ_SUC_REFL];
      COND_CASES_TAC THENL[
        RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
    	THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
        THEN REWRITE_TAC[ADD;LESS_EQ_MONO;ZERO_LESS_EQ];
    	MATCH_ACCEPT_TAC PWORDLEN1];
      ARITH_TAC;
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN IMP_RES_TAC LESS_OR;
      RESQ_REWRITE1_TAC WSEG_WSEG THENL[
       REWRITE_TAC[ADD_0;LESS_EQ_SUC_REFL];
       ARITH_TAC;
       REWRITE_TAC[ADD]]]);;

let WSEG_SHL_0 = prove_thm(`WSEG_SHL_0`,
    "!n. !w:* word :: PWORDLEN (SUC n). !m b.
     0 < m /\ m <= (SUC n) ==>
     (WSEG m 0 (SND (SHL f w b)) = 
     WCAT((WSEG (m - 1) 0 w), (f => WSEG 1 0 w |WORD[b])))",
    REPEAT GGEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SHL_DEF] 
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_EQ_MP PWORDLEN))
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN RESQ_REWRITE1_TAC (SPECL["n:num"; "1"] WSEG_WCAT_WSEG) THENL[
     RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
     THEN REWRITE_TAC[ADD_0;LESS_EQ_SUC_REFL];
     COND_CASES_TAC THENL[
      RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
      THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[(GSYM ADD1);ADD_0;LESS_EQ_MONO;ZERO_LESS_EQ];
      MATCH_ACCEPT_TAC PWORDLEN1];
     ASM_REWRITE_TAC[GSYM ADD1;ADD_0];
     CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
     CONV_TAC (ONCE_DEPTH_CONV num_CONV)
     THEN ASM_REWRITE_TAC[ADD_0;GSYM LESS_EQ];
     PURE_ONCE_REWRITE_TAC[ADD_0;SUB_0]
     THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
      RESQ_REWRITE1_TAC WSEG_WSEG THEN REWRITE_TAC[ADD_0;LESS_EQ_SUC_REFL]
      THEN ARITH_TAC;
      BOOL_CASES_TAC "f:bool" THEN REWRITE_TAC[] THENL[
       RESQ_REWRITE1_TAC WSEG_WSEG THEN REWRITE_TAC[ADD_0;LESS_EQ_SUC_REFL]
       THEN ARITH_TAC;
       RESQ_REWRITE1_TAC WSEG_WORD_LENGTH THEN TRY REFL_TAC
       THEN MATCH_ACCEPT_TAC PWORDLEN1]]]);;

close_theory();;



