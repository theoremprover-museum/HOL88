% ===================================================================== %
% FILE		: mk_wordn_num.ml					%
% DESCRIPTION   : Creates a theory of n-bit words as unsigned natural   %
%                 numbers.                                              %
% WRITES FILES	: wordn_num.th						%
%									%
% AUTHOR	: (c) T. Melham						%
% DATE		: 90.08.20					        %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Create the new theory                                                 %
% --------------------------------------------------------------------- %

new_theory `wordn_num`;;

% --------------------------------------------------------------------- %
% The bit-value of a boolean                                            %
% --------------------------------------------------------------------- %

let BV = new_definition(`BV`, "BV b = (b => SUC 0 | 0)");;

% --------------------------------------------------------------------- %
% The VAL function on boolean lists.                                    %
% --------------------------------------------------------------------- %

let VAL = new_recursive_definition false list_Axiom `VAL`
         "(VAL [] = 0) /\
          (!b bs. VAL (CONS b bs) = (BV b * 2 EXP (LENGTH bs)) + VAL bs)";;

% ===================================================================== %
% Theorems about VAL                                                    %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Theorem: largest unsigned n-bit natural number is less than 2^n       %
% --------------------------------------------------------------------- %

let VAL_LESS =
    prove_thm
    (`VAL_LESS`,
     "!l:(bool)list. VAL l < (2 EXP (LENGTH l))",
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [VAL;LENGTH;EXP;num_CONV "1";LESS_0];
      PURE_REWRITE_TAC [VAL;BV;EXP;LENGTH;TIMES2] THEN
      GEN_TAC THEN COND_CASES_TAC THEN 
      REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THENL
      [PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
       ASM_REWRITE_TAC [LESS_MONO_ADD_EQ];
       PURE_ONCE_REWRITE_TAC [ADD] THEN
       IMP_RES_THEN MATCH_ACCEPT_TAC LESS_IMP_LESS_ADD]]);;

% --------------------------------------------------------------------- %
% Theorem: largest unsigned n-bit natural does not exceed 2^n-1         %
% --------------------------------------------------------------------- %

let VAL_LESS_EQ =
    prove_thm
    (`VAL_LESS_EQ`,
     "!l:(bool)list. VAL l <= (2 EXP (LENGTH l)) - 1",
     GEN_TAC THEN SUBST1_TAC (num_CONV "2") THEN
     let tm = "(SUC 1) EXP (LENGTH (l:bool list))" in
     STRIP_ASSUME_TAC (SPEC tm num_CASES) THENL
     [IMP_RES_TAC NOT_EXP_0;
      let th = SUBS [num_CONV "2"] VAL_LESS in
      MP_TAC (SPEC "l:bool list" th) THEN
      ASM_REWRITE_TAC [SUC_SUB1;LESS_EQ;LESS_EQ_MONO]]);;

% --------------------------------------------------------------------- %
% Theorem: VAL is ont-to-one for equal-length lists.                    %
% --------------------------------------------------------------------- %

let VAL_ONE_ONE =
    prove_thm
    (`VAL_ONE_ONE`,
     "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (VAL l1 = VAL l2) ==> (l1 = l2)",
     let th1 = SYM (SPEC "2 EXP (LENGTH (l:bool list))" (CONJUNCT1 ADD)) in
     let thm = PURE_ONCE_REWRITE_RULE [th1] VAL_LESS in
     REPEAT (INDUCT_THEN list_INDUCT ASSUME_TAC ORELSE GEN_TAC) THENL
     [REPEAT DISCH_TAC THEN REFL_TAC;
      REWRITE_TAC [LENGTH; SUC_NOT];
      REWRITE_TAC [LENGTH; NOT_SUC];
      PURE_REWRITE_TAC [LENGTH;INV_SUC_EQ;VAL;CONS_11;BV] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      MAP_EVERY BOOL_CASES_TAC ["h:bool";"h':bool"] THENL
      [STRIP_TAC THEN ASM_REWRITE_TAC [EQ_MONO_ADD_EQ] THEN RES_TAC;
       REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES] THEN STRIP_TAC THEN
       DISCH_THEN (ASSUME_TAC o SYM) THEN
       MP_TAC (SPEC "l2:(bool)list" thm) THEN
       ASM_REWRITE_TAC [LESS_MONO_ADD_EQ;NOT_LESS_0];
       REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES] THEN STRIP_TAC THEN
       DISCH_TAC THEN MP_TAC (SPEC "l1:(bool)list" thm) THEN
       ASM_REWRITE_TAC [LESS_MONO_ADD_EQ;NOT_LESS_0];
       STRIP_TAC THEN RES_TAC THEN 
       ASM_REWRITE_TAC [LESS_MONO_ADD_EQ;ADD_0;MULT_CLAUSES]]]);;

let VAL_ONTO = prove_thm(`VAL_ONTO`, "!l. ?n. VAL l = n",
    LIST_INDUCT_TAC THENL[
    	EXISTS_TAC "0" THEN ACCEPT_TAC (CONJUNCT1 VAL);
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[VAL]
    	THEN POP_ASSUM CHOOSE_TAC
    	THEN EXISTS_TAC "((BV h) * (2 EXP (LENGTH (l:(bool)list)))) + n"
    	THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC]);;

% ===================================================================== %
% Definition of the WORDN function.                                     %
% ===================================================================== %

% --------------------------------------------------------------------- %
% Lemma: VAL l --> [0,...,2 ^ (LENGTH l) -1] is onto.                   %
% --------------------------------------------------------------------- %

let VAL_ONTO_LEMMA = prove_thm(`VAL_ONTO_LEMMA`,
    "!m n. n < (2 EXP m) ==> ?l. (LENGTH l = m) /\ (n = VAL l)",
     CONV_TAC (ONCE_DEPTH_CONV (num_CONV THENC (RAND_CONV num_CONV))) THEN
     INDUCT_TAC THEN PURE_REWRITE_TAC [EXP;MULT_CLAUSES;ADD_CLAUSES] THENL
     [GEN_TAC THEN REWRITE_TAC [num_CONV "1";LESS_THM;NOT_LESS_0] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC "NIL:(bool)list" THEN
      REWRITE_TAC [LENGTH;VAL];
      let th = SPECL ["n:num";"(SUC(SUC 0)) EXP m"]  LESS_OR_EQ_ADD in
      GEN_TAC THEN STRIP_ASSUME_TAC th THENL
      [STRIP_TAC THEN RES_THEN STRIP_ASSUME_TAC THEN
       EXISTS_TAC "CONS F l" THEN 
       ASM_REWRITE_TAC [LENGTH;VAL;ADD;BV;MULT_CLAUSES];
       ASM_REWRITE_TAC [LESS_MONO_ADD_EQ] THEN STRIP_TAC THEN
       RES_THEN STRIP_ASSUME_TAC THEN EXISTS_TAC "CONS T l" THEN
       let nth = (num_CONV THENC (RAND_CONV num_CONV)) "2" in
       ASM_REWRITE_TAC [LENGTH;VAL;nth;BV;ADD_CLAUSES;MULT_CLAUSES] THEN
       MATCH_ACCEPT_TAC ADD_SYM]]);;

% --------------------------------------------------------------------- %
% Lemma: VAL l --> {m MOD (2 EXP n)} is onto, where n = LENGTH l        %
% --------------------------------------------------------------------- %

let VAL_MOD_ONTO_LEMMA =
    TAC_PROOF
    (([], "!n m. ?l. (LENGTH l = n) /\ (VAL l = m MOD (2 EXP n))"),
     let th1 = SUBS [SYM(num_CONV "2")] (SPECL ["n:num";"1"] ZERO_LESS_EXP) in
     let thm = CONJUNCT2(SPEC "m:num" (MP (SPEC "2 EXP n" DIVISION) th1)) in
     REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (MATCH_MP VAL_ONTO_LEMMA thm) THEN
     EXISTS_TAC "l:bool list" THEN ASM_REWRITE_TAC []);;

% --------------------------------------------------------------------- %
% Lemma: the required WORDN function exists.                            %
% --------------------------------------------------------------------- %

let WORDN_EXISTS =
    TAC_PROOF
    (([], "?f. !n m. (LENGTH (f n m) = n) /\ (VAL(f n m) = m MOD (2 EXP n))"),
     EXISTS_TAC "\n m. @l. (LENGTH l = n) /\ (VAL l = m MOD 2 EXP n)" THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT GEN_TAC THEN CONV_TAC SELECT_CONV THEN
     MATCH_ACCEPT_TAC VAL_MOD_ONTO_LEMMA);;

% --------------------------------------------------------------------- %
% Introduce WORDN by the constant specification:                        %
%                                                                       %
% |- !n m.(LENGTH(WORDN n m) = n) /\ (VAL(WORDN n m) = m MOD (2 EXP n)) %
% --------------------------------------------------------------------- %

let WORDN = new_specification `WORDN` [`constant`,`WORDN`] WORDN_EXISTS;;

% ===================================================================== %
% Theorems about WORDN and VAL.                                         %
% ===================================================================== %

let WORDN_VAL =
    prove_thm
    (`WORDN_VAL`,
     "!l:bool list. WORDN (LENGTH l) (VAL l) = l",
     let th = SPECL ["LENGTH (l:bool list)";"VAL l"] WORDN in
     GEN_TAC THEN STRIP_ASSUME_TAC th THEN
     IMP_RES_TAC VAL_ONE_ONE THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC LESS_MOD THEN
     MATCH_ACCEPT_TAC VAL_LESS);;

% WORDN_0_N = |- !m. WORDN 0 m = [] %
let WORDN_0_N = GEN_ALL (PURE_REWRITE_RULE[LENGTH_NIL]
    (CONJUNCT1 (SPECL ["0";"m:num"] WORDN)));;

let WORDN_N_0 = TAC_PROOF(([],
    "!n. WORDN (SUC n) 0 = (CONS F (WORDN n 0))"),
    let lem = PURE_REWRITE_RULE[VAL;BV;LENGTH;ADD_CLAUSES;EXP;
    	    COND_CLAUSES;MULT] (SPEC "[F]" WORDN_VAL) in
    let lem' = PURE_REWRITE_RULE[VAL;BV;LENGTH;ADD_CLAUSES;COND_CLAUSES;
    	    MULT;WORDN] (SPEC "CONS F (CONS F (WORDN n 0))" WORDN_VAL) in
    INDUCT_TAC THENL[
    	REWRITE_TAC[lem;WORDN_0_N];
    	POP_ASSUM SUBST1_TAC THEN SUBST1_TAC (SYM lem')
    	THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV
    	THEN MATCH_MP_TAC ZERO_MOD THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP]);;

let WORDN_0 = save_thm(`WORDN_0`,
    CONJ WORDN_0_N WORDN_N_0);;


let WORDN_MOD = prove_thm(`WORDN_MOD`,
    "!n m. (WORDN n m) = (WORDN n (m MOD (2 EXP n)))",
    REPEAT GEN_TAC THEN SUBST1_TAC (SYM(CONJUNCT2 (SPEC_ALL WORDN)))
    THEN SUBST_OCCS_TAC [[2],(SYM(CONJUNCT1 (SPEC_ALL WORDN)))]
    THEN CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC WORDN_VAL);;

close_theory();;
