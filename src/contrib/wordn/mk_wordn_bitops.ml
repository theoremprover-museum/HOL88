% ===================================================================== %
% FILE		: mk_wordn_bitops.ml					%
% DESCRIPTION   : theory of wordn bitwise logical operations.		%
% WRITES FILES	: wordn_bitops.th					%
%									%
% AUTHOR	: (c) W. Wong						%
% DATE		: 23 March 1992						%
% ===================================================================== %

new_theory `wordn_bitops`;;

let MAP_INV = prove_thm(`MAP_INV`,
    "!f:*->*. (!x. f (f x) = x) ==> (!l. MAP f (MAP f l) = l)",
    GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN PURE_REWRITE_TAC[MAP] THENL[ REFL_TAC;
    	GEN_TAC THEN ASM_REWRITE_TAC[]]);;

%< MAP2 is defined in the system in Ver. 2.01 
let MAP2_DEF = new_list_rec_definition(`MAP2_DEF`,
    "(MAP2 (f:*->**->***) l [] = []) /\
     (MAP2 f l (CONS h t) = 
    	(NULL l) => [] | CONS (f (HD l) h) (MAP2 f (TL l) t))");;

% |- (!f. MAP2 f[][] = []) /\
   (!f h l h' l'.
     MAP2 f(CONS h l)(CONS h' l') = CONS(f h h')(MAP2 f l l')) %

let MAP2 = save_thm(`MAP2`, CONJ 
    (GEN_ALL (SPECL ["(f:*->**->***)"; "[]:(*)list"] (CONJUNCT1 MAP2_DEF)))
    (GEN_ALL (PURE_REWRITE_RULE[HD;TL;NULL;COND_CLAUSES] 
     (SPECL ["(f:*->**->***)"; "(CONS h l):(*)list"; "h':**"; "l':(**)list"]
      (CONJUNCT2 MAP2_DEF)))));;
>%

let MAP2_EQ_LENGTH = prove_thm(`MAP2_EQ_LENGTH`,
    "!(f:*->**->***) l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (LENGTH(MAP2 f l1 l2) = LENGTH l2)",
    GEN_TAC THEN LIST_INDUCT_TAC THENL[
      LIST_INDUCT_TAC THENL[
    	DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REFL_TAC;
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN REWRITE_TAC[SUC_NOT]];
      GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[NOT_SUC];
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ]
    	THEN DISCH_TAC THEN RES_TAC]]);;


let MAP2_SYM = prove_thm(`MAP2_SYM`,
    "!f:*->*->**. (!x1 x2. f x1 x2 = f x2 x1) ==>
     !(l1:(*)list) (l2:(*)list). (LENGTH l1 = LENGTH l2) ==>
      (MAP2 f l1 l2 = MAP2 f l2 l1)",
    GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL[
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
    	THEN PURE_ONCE_REWRITE_TAC[LENGTH_NIL]
    	THEN DISCH_THEN SUBST1_TAC
    	THEN PURE_ONCE_REWRITE_TAC[(CONJUNCT1 MAP2)]THEN REFL_TAC;
    	GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	    PURE_ONCE_REWRITE_TAC[LENGTH]
    	    THEN PURE_ONCE_REWRITE_TAC[LENGTH_NIL]
    	    THEN REWRITE_TAC[NOT_SUC];
    	    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2;LENGTH]
    	    THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ]
    	    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    	    THEN PURE_ONCE_REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL[
    	    	FIRST_ASSUM MATCH_ACCEPT_TAC; REFL_TAC]]]);;

let MAP2_ASSOC = prove_thm(`MAP2_ASSOC`,
    "!f:*->*->*. (!x1 x2 x3. f x1 (f x2 x3) = f (f x1 x2) x3) ==>
     !l1 l2 l3. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
      (MAP2 f l1 (MAP2 f l2 l3) = MAP2 f (MAP2 f l1 l2) l3)",
    let lem = GEN_ALL (CONV_RULE SYM_CONV (RIGHT_CONV_RULE SYM_CONV
    	 (CONV_RULE SYM_CONV (SPEC_ALL LENGTH_NIL)))) in
    GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL[
      REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
      THEN PURE_ONCE_REWRITE_TAC[lem]
      THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
      THEN POP_ASSUM SUBST1_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
      THEN PURE_ONCE_REWRITE_TAC[lem] THEN DISCH_THEN SUBST1_TAC
      THEN PURE_ONCE_REWRITE_TAC[MAP2] THEN REFL_TAC;
      GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	GEN_TAC THEN PURE_REWRITE_TAC[LENGTH]
    	THEN REWRITE_TAC[NOT_SUC];
        GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	  PURE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[NOT_SUC];
    	  GEN_TAC THEN PURE_REWRITE_TAC[LENGTH]
    	  THEN PURE_REWRITE_TAC[INV_SUC_EQ;MAP2]
    	  THEN STRIP_TAC THEN RES_TAC THEN PURE_REWRITE_TAC[CONS_11]
    	  THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]]);;

letrec LEFT_MOST_CONV conv tm =
    FIRST_CONV
    	[RATOR_CONV (LEFT_MOST_CONV conv);
    	 RAND_CONV (LEFT_MOST_CONV conv);
    	 ABS_CONV (LEFT_MOST_CONV conv); conv] tm;;

let PURE_ONCE_LEFT_MOST_REWRITE_TAC =
    GEN_REWRITE_TAC LEFT_MOST_CONV [];;


%-----------------------------------------------------------------------%
% The constants defined below perform bitwise logical operations on 	%
% n-bit words. They actually operate on the representation type, namely	%
% :(bool)list. Operators for each specific word length should be defined%
% based on these generic operators. 					%
%-----------------------------------------------------------------------%

% NOTN: generic bitwise NOT	    	    				%

let NOTN_DEF = new_definition(`NOTN_DEF`,
    "(NOTN (l:(bool)list) = MAP ($~) l)");;

let NOTN = prove_thm(`NOTN`, "!l. NOTN (NOTN l) = l",
    PURE_REWRITE_TAC[NOTN_DEF] THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[MAP]);;

% ANDN: generic bitwise AND	    	    			%

let ANDN_DEF = new_definition(`ANDN_DEF`,
    "ANDN (l1:(bool)list) (l2:(bool)list) = MAP2 ($/\) l1 l2");;
    	    	

let ANDN_SYM = prove_thm(`ANDN_SYM`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (ANDN l1 l2 = ANDN l2 l1)",
    REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[ANDN_DEF]
    THEN ASSUME_TAC CONJ_SYM THEN IMP_RES_TAC MAP2_SYM);;

let ANDN_ASSOC = prove_thm(`ANDN_ASSOC`,
    "!l1 l2 l3. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
     (ANDN l1 (ANDN l2 l3) = ANDN (ANDN l1 l2) l3)",
    REPEAT STRIP_TAC THEN PURE_REWRITE_TAC[ANDN_DEF]
    THEN ASSUME_TAC CONJ_ASSOC THEN IMP_RES_TAC MAP2_ASSOC);;
    	    
% ORN: generic bitwise OR    	    					%

let ORN_DEF = new_definition(`ORN_DEF`,
     "ORN l1 l2 = MAP2 ($\/) l1 l2");;

let ORN_SYM = prove_thm(`ORN_SYM`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (ORN l1 l2 = ORN l2 l1)",
    REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[ORN_DEF]
    THEN ASSUME_TAC DISJ_SYM THEN IMP_RES_TAC MAP2_SYM);;

let ORN_ASSOC = prove_thm(`ORN_ASSOC`,
    "!l1 l2 l3. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
     (ORN l1 (ORN l2 l3) = ORN (ORN l1 l2) l3)",
    REPEAT STRIP_TAC THEN PURE_REWRITE_TAC[ORN_DEF]
    THEN ASSUME_TAC DISJ_ASSOC THEN IMP_RES_TAC MAP2_ASSOC);;

% XORN: generic bitwise XOR	    	    					%

let XORN_DEF = new_definition(`XORN_DEF`,
     "XORN (l1:(bool)list) l2 = MAP2 (\x x'. ~(x = x')) l1 l2");;


let XOR_SYM = prove_thm(`XOR_SYM`,
    "!x1 (x2:bool). (\x x'. ~(x = x')) x1 x2 = (\x x'. ~(x = x')) x2 x1",
    REPEAT GEN_TAC THEN BETA_TAC THEN EQ_TAC
    THEN DISCH_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
    THEN FIRST_ASSUM ACCEPT_TAC);;

let XORN_SYM = prove_thm(`XORN_SYM`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (XORN l1 l2 = XORN l2 l1)",
    REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[XORN_DEF]
    THEN ASSUME_TAC XOR_SYM THEN IMP_RES_TAC MAP2_SYM);;

let XOR_ASSOC = prove_thm(`XOR_ASSOC`,
    "!(x1:bool) x2 x3. (\x x'. ~(x = x')) x1 ((\x x'. ~(x = x')) x2 x3) =
     (\x x'. ~(x = x')) ((\x x'. ~(x = x')) x1 x2) x3",
    REPEAT GEN_TAC THEN BETA_TAC
    THEN MAP_EVERY BOOL_CASES_TAC ["x1:bool"; "x2:bool"; "x3:bool"]
    THEN PURE_REWRITE_TAC[NOT_CLAUSES;EQ_CLAUSES]);;

let XORN_ASSOC = prove_thm(`XORN_ASSOC`,
    "!l1 l2 l3. (LENGTH l1 = LENGTH l2) /\ (LENGTH l2 = LENGTH l3) ==>
     (XORN l1 (XORN l2 l3) = XORN (XORN l1 l2) l3)",
    REPEAT STRIP_TAC THEN PURE_REWRITE_TAC[XORN_DEF]
    THEN ASSUME_TAC XOR_ASSOC THEN IMP_RES_TAC MAP2_ASSOC);;

let LENGTH_NOTN = prove_thm(`LENGTH_NOTN`,
    "!l. LENGTH(NOTN l) = LENGTH l",
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NOTN_DEF]
    THEN MATCH_ACCEPT_TAC LENGTH_MAP);;

let LENGTH_ANDN = prove_thm(`LENGTH_ANDN`,
    "!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     ((LENGTH (ANDN l1 l2)) = (LENGTH l2))",
    REPEAT GEN_TAC THEN PURE_REWRITE_TAC[ANDN_DEF]
    THEN MATCH_ACCEPT_TAC MAP2_EQ_LENGTH);;

let LENGTH_ORN = prove_thm(`LENGTH_ORN`,
    "!l1 l2.  (LENGTH l1 = LENGTH l2) ==>
     ((LENGTH (ORN l1 l2)) = (LENGTH l2))",
    REPEAT GEN_TAC THEN PURE_REWRITE_TAC[ORN_DEF]
    THEN MATCH_ACCEPT_TAC MAP2_EQ_LENGTH);;

let LENGTH_XORN = prove_thm(`LENGTH_XORN`,
    "!l1 l2.  (LENGTH l1 = LENGTH l2) ==>
     ((LENGTH (XORN l1 l2)) = (LENGTH l2))",
    REPEAT GEN_TAC THEN PURE_REWRITE_TAC[XORN_DEF]
    THEN MATCH_ACCEPT_TAC MAP2_EQ_LENGTH);;

close_theory();;

