% ===================================================== %
% FILE: mk_word_num.ml	    DATE: 14 Aug 1992		%
% AUTHOR: Wai WONG  	    	    			%
% Writes: word_base.th	    	    			%
% Uses: Libraries: arith res_quan			%
% Description: Creates a theorey for mapping between 	%
% natural numbers and generic words	    	    	%
% ===================================================== %
% Revised and updated for HOL 2.02 on 7 Feb. 1994 by WW	%

loadt(`ver_`^(string_of_int(version())));;

load_theory`word_base`;;
map autoload_all [`word_base`];;

new_theory`word_num`;;

loadf`word_funs`;;

%---------------------------------------------------------------%
% Mapping between word and num 	    				%
%---------------------------------------------------------------%

% LVAL f b [bn-1;...;b0] returns the value represnted by a list of digits. %
% where b is the base and f is the function mapping the digit to its value %

let LVAL_DEF = new_definition(`LVAL_DEF`,
    "LVAL (f:*->num) b l = FOLDL (\e x. (b * e) + (f x)) 0 l");;

let LVAL = prove_thm(`LVAL`,
    "(!f:*->num. !b. LVAL f b [] = 0) /\
     (!l. !f:*->num. !b x. LVAL f b (CONS (x:*) l) =
      ((f x) * (b EXP (LENGTH l))) + (LVAL f b l))",
    REWRITE_TAC [LVAL_DEF;FOLDL;MULT_CLAUSES;ADD_CLAUSES]
    THEN BETA_TAC THEN REWRITE_TAC[LENGTH;MULT_CLAUSES;ADD_CLAUSES] 
    THEN SNOC_INDUCT_TAC THEN REPEAT GEN_TAC THENL[
      REWRITE_TAC[FOLDL;LENGTH;MULT_CLAUSES;EXP;ADD_CLAUSES];
      REWRITE_TAC[FOLDL_SNOC;LENGTH_SNOC;MULT_CLAUSES;EXP;ADD_CLAUSES]
      THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_ASSOC]
      THEN SUBST1_TAC (SPECL["(f:*->num) x''";"b:num"]MULT_SYM)
      THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
      THEN ASM_REWRITE_TAC[]]);;

let NVAL_DEF = new_recursive_definition false word_Ax `NVAL_DEF`
    "NVAL f b (WORD l:* word) = LVAL f b l";;

let LVAL_SNOC = prove_thm(`LVAL_SNOC`,
    "!l:* list. !h f b.
     LVAL f b (SNOC h l) = (((LVAL f b l)* b) + (f h))",
    LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC;LVAL;
    	MULT;ADD_CLAUSES;LENGTH;LENGTH_SNOC;EXP;MULT_CLAUSES]
    THEN REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN CONV_TAC ((RAND_CONV o ONCE_DEPTH_CONV) (REWR_CONV (GSYM MULT_ASSOC)))
    THEN SUBST1_TAC (SPECL["b EXP (LENGTH (l:* list))"; "b:num"] MULT_SYM)
    THEN MATCH_ACCEPT_TAC ADD_ASSOC);;

let LESS_SUC_IMP_LESS_EQ = GEN_ALL (TRANS (SPEC_ALL LESS_THM)
    (PURE_ONCE_REWRITE_RULE[DISJ_SYM](SYM (SPEC_ALL LESS_OR_EQ))));;

let LVAL_MAX_lem = PROVE(
    "!a b c y. ((a+b)<SUC c) /\ (y < b) ==> ((a+y) < c)",
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LESS_SUC_IMP_LESS_EQ]
    THEN STRIP_TAC THEN IMP_RES_THEN (ASSUME_TAC o 
    	(SPEC "a:num") o (PURE_ONCE_REWRITE_RULE[ADD_SYM])) LESS_MONO_ADD
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS);;

let LESS_MULT_PLUS_DIFF = PROVE(
   "!n k l . (k < l) ==> (((k * n) + n) <= (l * n))",
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;LESS_EQ_REFL] THEN
  DISCH_THEN \t . 
    REPEAT GEN_TAC THEN
    DISCH_THEN \t'.
         ACCEPT_TAC 
         (REWRITE_RULE [ADD_CLAUSES;ADD_ASSOC]
           (MATCH_MP LESS_EQ_LESS_EQ_MONO
             (CONJ (MATCH_MP LESS_OR t') (MATCH_MP t t')))) );;

let LVAL_MAX = prove_thm(`LVAL_MAX`,
    "!(l:* list) f b. (!x. f x < b) ==> ((LVAL f b l) < (b EXP (LENGTH l)))",
    LIST_INDUCT_TAC THEN REPEAT STRIP_TAC 
    THEN PURE_REWRITE_TAC[LVAL;LENGTH;EXP] THENL[
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0;
      let lem1 = GEN "a:num"(SPECL["a:num";"b EXP (LENGTH (l:* list))";
    	"b * (b EXP (LENGTH (l:* list)))";"LVAL f b (l:* list)"]
    	LVAL_MAX_lem) in
      RES_THEN MP_TAC THEN POP_ASSUM (ASSUME_TAC o (SPEC"h:*"))
      THEN DISCH_TAC THEN MATCH_MP_TAC lem1 THEN CONJ_TAC
      THEN (MAP_EVERY MATCH_MP_TAC [LESS_EQ_IMP_LESS_SUC;
        LESS_MULT_PLUS_DIFF] ORELSE ALL_TAC)
      THEN FIRST_ASSUM ACCEPT_TAC]);;

let NVAL_MAX = prove_thm(`NVAL_MAX`,
    "!f b. (!x. f x < b) ==>
     !n. !w:* word ::PWORDLEN n. NVAL f b w < (b EXP n)",
    REPEAT STRIP_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[NVAL_DEF] THEN FIRST_ASSUM SUBST1_TAC
    THEN MATCH_MP_TAC LVAL_MAX THEN FIRST_ASSUM ACCEPT_TAC);;

let NVAL0 = prove_thm(`NVAL0`,
    "!f b. NVAL f b (WORD[]:(*)word) = 0",
    REWRITE_TAC[NVAL_DEF;LVAL]);;

let NVAL1 = prove_thm(`NVAL1`,
    "!f b (x:*). NVAL f b (WORD[x]) = (f x)",
    REWRITE_TAC[NVAL_DEF;LVAL;LENGTH;EXP;MULT_CLAUSES;ADD_CLAUSES]);;

let NVAL_WORDLEN_0 = prove_thm(`NVAL_WORDLEN_0`,
    "!w:(*)word::PWORDLEN 0. !fv r. NVAL fv r w = 0",
    RESQ_GEN_TAC THEN IMP_RES_THEN SUBST1_TAC PWORDLEN0
    THEN REWRITE_TAC[NVAL_DEF;LVAL]);;

let NVAL_WCAT1 = prove_thm(`NVAL_WCAT1`,
    "!w:(*)word. !f b x.
     NVAL f b (WCAT (w,WORD[x])) = ((NVAL f b w) * b)  + (f x)",
    word_INDUCT_TAC THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[NVAL_DEF;WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
    THEN MATCH_ACCEPT_TAC LVAL_SNOC);;

let NVAL_WCAT2 = prove_thm(`NVAL_WCAT2`,
    "!n. !w:(*)word::PWORDLEN n. !f b x. 
     NVAL f b (WCAT (WORD[x],w)) = ((f x) * (b EXP n)) + (NVAL f b w)",
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[NVAL_DEF;WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM CONS_APPEND]
    THEN MATCH_ACCEPT_TAC (CONJUNCT2 LVAL));;

let NVAL_WCAT = prove_thm(`NVAL_WCAT`,
    "!n m. !w1:(*)word::PWORDLEN n. !w2:(*)word::PWORDLEN m. !f b.
     NVAL f b (WCAT (w1,w2)) = ((NVAL f b w1) * (b EXP m)) + (NVAL f b w2)",
    let deres = (GEN_ALL o RESQ_HALF_SPEC o SPEC_ALL) in
    let lem1 = deres NVAL_WCAT2 in
    let lem2 = (REWRITE_RULE[ADD_0;LESS_EQ_SUC_REFL](SPECL["n:num";"0"]
    	 (RESQ_SPEC "w1:(*)word"(SPEC "SUC n" WSEG_PWORDLEN)))) in
    INDUCT_TAC THEN GEN_TAC THEN REPEAT GGEN_TAC THENL[
     IMP_RES_THEN SUBST1_TAC PWORDLEN0
     THEN PURE_REWRITE_TAC[WCAT0;NVAL0;ADD;MULT] THEN REFL_TAC;
     RESQ_IMP_RES_THEN SUBST1_TAC WORDLEN_SUC_WCAT_BIT_WSEG
     THEN PURE_ONCE_REWRITE_TAC[GSYM WCAT_ASSOC]
     THEN PURE_ONCE_REWRITE_TAC[MATCH_MP lem1 lem2]
     THEN FIRST_ASSUM (ASSUME_TAC o
    	 (MATCH_MP (deres(MATCH_MP (deres WCAT_PWORDLEN) lem2))))
     THEN POP_ASSUM (\t. PURE_ONCE_REWRITE_TAC[MATCH_MP lem1 t])
     THEN FIRST_ASSUM (\t. ASSUME_TAC(MATCH_MP (deres t)lem2))
     THEN POP_ASSUM (\t1. POP_ASSUM (\t2.
    	PURE_ONCE_REWRITE_TAC[MATCH_MP (deres t1) t2]))
     THEN CONV_TAC (LHS_CONV (REWR_CONV ADD_ASSOC))
     THEN CONV_TAC (REWR_CONV EQ_MONO_ADD_EQ)
     THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
     THEN CONV_TAC (REWR_CONV EQ_MONO_ADD_EQ)
     THEN PURE_ONCE_REWRITE_TAC[EXP_ADD]
     THEN MATCH_ACCEPT_TAC MULT_ASSOC]);;

% NLIST n fmod b m returns a list of length n which represents the value m %
% where b is the base and fmod is the remainder function converting a value%
% to fit in a digit.	    	    					   %

let NLIST_DEF = new_prim_rec_definition(`NLIST_DEF`,
    "(NLIST 0 (frep:num->*) b m = []) /\
     (NLIST (SUC n) frep b m =
       SNOC (frep (m MOD b)) (NLIST n frep b (m DIV b)))");;

let NWORD_DEF = new_definition(`NWORD_DEF`,
    "NWORD n (frep:num->*) b m = WORD(NLIST n frep b m)");;

let NLIST_LENGTH = PROVE(
    "!n (f:num->*) b m. LENGTH(NLIST n f b m) = n",
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[NLIST_DEF]
    THEN ASM_REWRITE_TAC[LENGTH;LENGTH_SNOC]);;

let NWORD_LENGTH = prove_thm(`NWORD_LENGTH`,
    "!n (f:num->*) b m. WORDLEN(NWORD n f b m) = n",
    REWRITE_TAC[NWORD_DEF;WORDLEN_DEF;NLIST_LENGTH]);;

let NWORD_PWORDLEN = prove_thm(`NWORD_PWORDLEN`,
    "!n (f:num->*) b m. PWORDLEN n (NWORD n f b m)",
    REWRITE_TAC[PWORDLEN_DEF;NWORD_DEF;NLIST_LENGTH]);;

close_theory();;
