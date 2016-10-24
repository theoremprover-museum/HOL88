% HOL88 version : completed 31/v/89 RCO %
% HOL12 version : completed 18/3/91 RCO %
% FILE		: int.ml	 					%
% DESCRIPTION   : Theory of the integers.				%
%									%
% READS FILES	: tydefs.th tydefs.ml mod.th da.th wop.th		%
% WRITES FILES	: int.th						%
%									%
% AUTHOR	: (c) T. Melham 1987					%
% DATE		: 87.10.25						%
%									%
% NOTE: preliminary theory only, please do not circulate!		%


% Create the new theory							%
new_theory `int`;;

% parent is type definition theory.					%
new_parent `tydefs`;;

% mod (and da and wop) are also parents					%
new_parent `mod`;;

new_parent `arith`;;
load_theorems`arith`;;

% load type definition package						%
% map loadf [`tydefs`;`tyfns`];; %

% load wop.								%
let Wop = theorem `arithmetic` `WOP`;;

% load da.								%
let Da = theorem `da` `Da`;;
let Remainder_Unique = theorem `da` `Remainder_Unique`;;
let Quotient_Unique = theorem `da` `Quotient_Unique`;;

% Define the integers.							%
let Int_Axiom = 
    define_type `Int_Axiom` `int = Int num | Nint num`;;

% prove induction theorem for int.					%
let int_Induct = 
    save_thm (`int_Induct`,prove_induction_thm Int_Axiom);;

% prove cases theorem for int.						%
let int_cases = 
    save_thm (`int_cases`, prove_cases_thm int_Induct);;

% prove that the constructors for int are one-to-one			%
let [Int_11;Nint_11] = 
    let [th1;th2] = (CONJUNCTS (prove_constructors_one_one Int_Axiom)) in
        map save_thm [`Int_11`,th1;`Nint_11`,th2];;

% Prove that the constructors are distinct.				%
let int_constr_distinct = 
    save_thm (`int_constr_distinct`, prove_constructors_distinct Int_Axiom);;

% Define negation.							%
let neg_DEF  = new_recursive_definition false Int_Axiom `neg_DEF`
	       "(neg (Int n) = ((0 < n) => Nint(PRE n) | Int 0)) /\
	        (neg (Nint n) = Int (SUC n))";;

% define test for positive integers.					%
let Pos_DEF  = new_recursive_definition false Int_Axiom `Pos_DEF`
	       "(Pos (Int n) = (0 < n)) /\
	        (Pos (Nint n) = F)";;

% define test for negative integers.					%
let Neg_DEF  = new_recursive_definition false Int_Axiom `Neg_DEF`
	       "(Neg (Int n) = F) /\
	        (Neg (Nint n) = T)";;

% define test for zero.							%
let Zero_DEF  = new_recursive_definition false Int_Axiom `Zero_DEF`
	       "(Zero (Int n) = (n=0)) /\
	        (Zero (Nint n) = F)";;

% define destructor for integers					%
let abs_DEF  = new_recursive_definition false Int_Axiom `abs_DEF`
	       "(abs (Int n) = n) /\
	        (abs (Nint n) = SUC n)";;

% define addition.							%
let plus_DEF = 
    new_recursive_definition true Int_Axiom `plus_DEF`   
    "(plus (Int n)  i = ((Neg i)        => 
    		        (((abs i) <= n) => (Int (n - (abs i))) |
		      		           (Nint (PRE((abs i) - n)))) | 
				           (Int (n + (abs i))))) /\
     (plus (Nint n) i = ((Neg i)        => (Nint (n + abs i)) |
     			((n <  (abs i)) => (Int ((abs i) - abs(Nint n))) | 
			 		   (Nint (n - (abs i))))))";;


% Prove a theorem about the various addition cases			%

let plus_THM = 
    prove_thm
    (`plus_THM`,
     "(!n m. (Int n) plus (Int m) = Int (n + m)) /\
      (!n m. (Int n) plus (Nint m) = 
	     (m < n => Int ((n - m) - 1) | Nint(m - n))) /\
      (!n m. (Nint n) plus (Int m) = 
	     (n < m => Int ((m - n) - 1) | Nint(n - m))) /\
      (!n m. (Nint n) plus (Nint m) = Nint (SUC(n + m)))",
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC [plus_DEF;Neg_DEF;abs_DEF];
      REWRITE_TAC [plus_DEF;Neg_DEF;abs_DEF;PRE_SUB;PRE;LESS_EQ] THEN
      REWRITE_TAC [ADD1;SUB_PLUS];
      REWRITE_TAC [plus_DEF;Neg_DEF;abs_DEF;PRE_SUB;PRE;LESS_EQ] THEN
      REWRITE_TAC [ADD1;SUB_PLUS];
      REWRITE_TAC [plus_DEF;Neg_DEF;abs_DEF;ADD_CLAUSES]]);;

% Prove that addition is commutative.					%
let plus_COMM = 
    prove_thm
    (`plus_COMM`,
     "!i j. i plus j = j plus i",
     REPEAT ((INDUCT_THEN int_Induct ASSUME_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [plus_THM] THENL
     [AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM;
      AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC ADD_SYM]);;

% Prove that Int 0 is the identity.					%
let plus_ID = 
    prove_thm
    (`plus_ID`,
     "!i. (i plus (Int 0) = i) /\ ((Int 0) plus i = i)",
     INDUCT_THEN int_Induct ASSUME_TAC THEN
     REWRITE_TAC [plus_THM;ADD_CLAUSES;NOT_LESS_0;SUB_0]);;

% prove that neg gives the additive inverse				%
let plus_INV = 
    prove_thm
    (`plus_INV`,
     "!i. (i plus (neg i) = Int 0) /\ ((neg i) plus  i = Int 0)",
     INDUCT_THEN int_Induct ASSUME_TAC THEN
     REWRITE_TAC [neg_DEF;plus_THM;NOT_LESS_0] THENL
     [GEN_TAC THEN STRIP_ASSUME_TAC (SPEC "n:num" num_CASES) THENL
      [ASM_REWRITE_TAC [LESS_REFL;plus_THM;ADD_CLAUSES];
       ASM_REWRITE_TAC [plus_THM;LESS_0;PRE;LESS_SUC_REFL] THEN  
       REWRITE_TAC [ADD1;SYM(SPEC_ALL SUB_PLUS);SUB_EQUAL_0]];
       REWRITE_TAC [LESS_SUC_REFL;ADD1;SYM(SPEC_ALL SUB_PLUS);SUB_EQUAL_0]]);;

% Prove that -(- i) = i							%
let neg_neg_THM = 
    prove_thm
    (`neg_neg_THM`,
     "!i. neg(neg i) = i",
     INDUCT_THEN int_Induct ASSUME_TAC THEN
     REWRITE_TAC [neg_DEF;LESS_0;PRE] THEN
     GEN_TAC THEN STRIP_ASSUME_TAC (SPEC "n:num" num_CASES) THENL
     [ASM_REWRITE_TAC [LESS_REFL;neg_DEF];
      ASM_REWRITE_TAC [LESS_0;neg_DEF;PRE]]);;

% Prove that plus is associative.  Done by cases.			%

% + + + case								%
let assoc_lemma1 = 
    TAC_PROOF
    (([], "!n m p. (Int n) plus ((Int m) plus (Int p)) = 
		  ((Int n) plus (Int m)) plus (Int p)"),
     REWRITE_TAC [plus_THM;ADD_ASSOC]);;

% + + - case								%

let assoc_lemma2 = 
    TAC_PROOF
    (([], "!n m p. (Int n) plus ((Int m) plus (Nint p)) = 
		  ((Int n) plus (Int m)) plus (Nint p)"),
     PURE_REWRITE_TAC [plus_THM] THEN
     REPEAT GEN_TAC THEN ASM_CASES_TAC "p < m" THENL
     [IMP_RES_TAC LESS_IMP_LESS_ADD THEN
%was REWRITE1_TAC o ... %
      POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
      ASM_REWRITE_TAC[plus_THM;SYM(SPEC_ALL SUB_PLUS);SYM(SPEC_ALL ADD1)] THEN
      IMP_RES_TAC LESS_OR THEN IMP_RES_TAC LESS_EQ_ADD_SUB THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC [plus_THM] THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
      IMP_RES_TAC LESS_EQ_SUB_LESS THEN 
%was POP_ASSUM REWRITE1_TAC %
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SYM(SPEC_ALL SUB_PLUS);SYM(SPEC_ALL ADD1)] THEN      
      SUBST_OCCS_TAC [[1;3], SPECL ["n:num";"m:num"] ADD_SYM] THEN
      REWRITE_TAC [ADD1;SUB_PLUS] THEN
      IMP_RES_TAC SUB_SUB THEN ASM_REWRITE_TAC[]]);;

% - - + case								%
% modified by rco 18/iii/91 to run in HOL12                             %
let assoc_lemma3 = 
    TAC_PROOF
    (([], "!n m p. (Nint n) plus ((Nint m) plus (Int p)) = 
		  ((Nint n) plus (Nint m)) plus (Int p)"),
     PURE_REWRITE_TAC [plus_THM] THEN
     REPEAT GEN_TAC THEN ASM_CASES_TAC "m < p" THENL
     [ASM_REWRITE_TAC [plus_THM;SYM(SPEC_ALL SUB_PLUS)] THEN
      REWRITE_TAC [num_CONV "1";ADD_CLAUSES] THEN
      ASM_CASES_TAC "n < (p - (SUC m))" THENL
      [IMP_RES_TAC LESS_SUB_ADD_LESS THEN 
       POP_ASSUM(ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES]) THEN
       SUBST1_TAC (SPECL ["m:num";"n:num"] ADD_SYM) THEN ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [] THEN
       POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
       IMP_RES_TAC LESS_OR THEN IMP_RES_TAC SUB_SUB THEN
       IMP_RES_TAC SUB_LESS_EQ_ADD THEN
       UNDISCH_TAC "p <= ((SUC m) + n)" THEN DISCH_TAC THEN
       POP_ASSUM (ASSUME_TAC o REWRITE_RULE [ADD_CLAUSES]) THEN
       POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE[ADD_SYM]) THEN
       POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [SYM(SPEC_ALL NOT_LESS)])) THEN
       ASM_REWRITE_TAC[ADD_CLAUSES]];
      ASM_REWRITE_TAC [plus_THM;SYM(SPEC_ALL SUB_PLUS)] THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
      IMP_RES_TAC LESS_EQ_ADD_SUB THEN
      ASM_REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      ASSUME_TAC (SPECL ["m:num";"SUC n"] LESS_EQ_ADD) THEN
      IMP_RES_TAC (SPECL ["p:num";"m:num";"m + (SUC n)"] LESS_EQ_TRANS) THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [SYM(SPEC_ALL NOT_LESS)]) THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_REWRITE_TAC[]]);;

% - - - case								%

let assoc_lemma4 = 
    TAC_PROOF
    (([], "!n m p. (Nint n) plus ((Nint m) plus (Nint p)) = 
		  ((Nint n) plus (Nint m)) plus (Nint p)"),
     REWRITE_TAC [ADD_ASSOC;ADD_CLAUSES;plus_THM]);;

% Prove that addition is associative.					%
let plus_ASSOC = 
    prove_thm
    (`plus_ASSOC`,
     "!i j k. i plus (j plus k) = (i plus j) plus k",
      REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THENL
      [MATCH_ACCEPT_TAC assoc_lemma1;
       MATCH_ACCEPT_TAC assoc_lemma2;
       PURE_ONCE_REWRITE_TAC [SPEC "Nint n" plus_COMM] THEN
       PURE_ONCE_REWRITE_TAC [assoc_lemma2] THEN
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Int n"] plus_COMM] THEN
       REWRITE_TAC [assoc_lemma2];
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] plus_COMM] THEN
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] plus_COMM] THEN
       PURE_ONCE_REWRITE_TAC [assoc_lemma3] THEN 
       SUBST1_TAC (SPECL ["Nint n'";"Nint n''"] plus_COMM) THEN
       MATCH_ACCEPT_TAC plus_COMM;
       PURE_ONCE_REWRITE_TAC [SPEC "Nint n" plus_COMM] THEN
       SUBST1_TAC (SPECL ["Int n'";"Int n''"] plus_COMM) THEN
       REWRITE_TAC [SYM(SPEC_ALL assoc_lemma2)] THEN
       MATCH_ACCEPT_TAC plus_COMM;
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] plus_COMM] THEN
       REWRITE_TAC [assoc_lemma3] THEN
       SUBST1_TAC (SPECL ["Nint n";"Nint n''"] plus_COMM) THEN
       REFL_TAC;
       MATCH_ACCEPT_TAC assoc_lemma3;
       MATCH_ACCEPT_TAC assoc_lemma4]);;


let lemma = 
    CONJ (NOT_EQ_SYM(SPEC_ALL int_constr_distinct)) int_constr_distinct;;

let LEFT_plus_CANCEL = 
    prove_thm
    (`LEFT_plus_CANCEL`,
     "!k i j. (k plus i = k plus j) = (i = j)",
     REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [plus_THM;Int_11;Nint_11;lemma] THENL
     [PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_MONO_ADD_EQ;
      ASM_CASES_TAC "n''<n" THEN ASM_REWRITE_TAC [lemma;Int_11] THEN
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      SUBST1_TAC (SPECL ["n'':num";"p+1"] ADD_SYM) THEN 
        REWRITE_TAC [ADD_SUB] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);ADD_INV_0_EQ] THEN
      REWRITE_TAC [num_CONV "1";ADD_CLAUSES;NOT_SUC];
      ASM_CASES_TAC "n'<n" THEN ASM_REWRITE_TAC [Int_11;lemma] THEN
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      SUBST1_TAC (SPECL ["n':num";"p+1"] ADD_SYM) THEN 
         REWRITE_TAC [ADD_SUB] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);ADD_INV_0_EQ] THEN
      REWRITE_TAC [num_CONV "1";ADD_CLAUSES;NOT_SUC];
      ASM_CASES_TAC "n'<n" THEN ASM_CASES_TAC "n''<n" THEN 
      ASM_REWRITE_TAC [Int_11;lemma;SYM(SPEC_ALL SUB_PLUS);Nint_11] THENL
      [SUBST1_TAC (SYM (SPECL ["n':num";"n'':num";"1"] EQ_MONO_ADD_EQ)) THEN
       MATCH_MP_TAC SUB_CANCEL THEN 
       ASM_REWRITE_TAC (map (SYM o SPEC_ALL) [LESS_EQ;ADD1]);
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC;
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC;
       RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS]) THEN IMP_RES_TAC CANCEL_SUB];
      ASM_CASES_TAC "n<n'" THEN ASM_CASES_TAC "n<n''" THEN 
      ASM_REWRITE_TAC [Int_11;lemma;SYM(SPEC_ALL SUB_PLUS);Nint_11] THENL
      [MATCH_MP_TAC CANCEL_SUB THEN
       ASM_REWRITE_TAC [num_CONV "1";SYM(SPEC_ALL LESS_EQ);ADD_CLAUSES];
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC;
       DISCH_THEN SUBST_ALL_TAC THEN RES_TAC;
       RULE_ASSUM_TAC (REWRITE_RULE [NOT_LESS]) THEN IMP_RES_TAC SUB_CANCEL];
      ASM_CASES_TAC "n<n'" THEN ASM_REWRITE_TAC [Nint_11;lemma] THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
      POP_ASSUM (ASSUME_TAC o 
         (MP (SPECL ["SUC(n+n'')";"n':num";"n:num"] ADD_EQ_SUB))) THEN
% IMP_RES_TAC, was here before MP but is no good here for hol88 %
%      IMP_RES_TAC (SPEC "SUC(n + n'')" ADD_EQ_SUB) THEN %
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD_CLAUSES;SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 4 (CONJUNCTS ADD_CLAUSES))] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      MATCH_MP_TAC LESS_NOT_EQ THEN MATCH_ACCEPT_TAC LESS_ADD_SUC;
      ASM_CASES_TAC "n<n''" THEN ASM_REWRITE_TAC [Nint_11;lemma] THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
% remove this for hol88 %
%     IMP_RES_TAC (SPEC "SUC(n + n')" ADD_EQ_SUB) THEN %
      POP_ASSUM (ASSUME_TAC o
         (MP (SPECL ["SUC(n+n')";"n'':num";"n:num"] ADD_EQ_SUB)) ) THEN
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD_CLAUSES;SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 4 (CONJUNCTS ADD_CLAUSES))] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      MATCH_MP_TAC LESS_NOT_EQ THEN MATCH_ACCEPT_TAC LESS_ADD_SUC;
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [INV_SUC_EQ;EQ_MONO_ADD_EQ]]);;
     
let RIGHT_plus_CANCEL = 
    prove_thm
    (`RIGHT_plus_CANCEL`,
     "!k i j. (i plus k = j plus k) = (i = j)",
     PURE_ONCE_REWRITE_TAC [plus_COMM] THEN
     REWRITE_TAC [LEFT_plus_CANCEL]);;

let int_neg_CASES = 
    prove_thm
    (`neg_int_CASES`,
     "!i. (?n. i = Int n) \/ (?n. i = neg(Int (SUC n)))",
     INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC "n:num" THEN REFL_TAC;
      REWRITE_TAC [neg_DEF;PRE;LESS_0] THEN
      DISJ2_TAC THEN EXISTS_TAC "n:num" THEN REFL_TAC]);;

% define multiplication.						%
let times_DEF = 
 new_recursive_definition true Int_Axiom `times_DEF`   
 "(times (Int n)  i =
  ((n = 0) => Int 0 | ((Neg i) => Nint(PRE(n * abs i)) | Int (n * abs i)))) /\
  (times (Nint n) i = 
  ((i = Int 0) => Int 0 | 
  ((Neg i) => Int((SUC n) * abs i) | Nint (PRE((SUC n) * (abs i))))))";;

let times_THM = 
    prove_thm
    (`times_THM`,
     "(!n m. (Int n) times (Int m) = Int (n * m)) /\
      (!n m. (Int n) times (Nint m) = 
	     ((n = 0) => Int 0 | Nint(PRE(n * (SUC m))))) /\
      (!n m. (Nint n) times (Int m) = 
	     ((m = 0) => Int 0 | Nint(PRE(m * (SUC n))))) /\
      (!n m. (Nint n) times (Nint m) = Int ((SUC n) * (SUC m)))",
     REWRITE_TAC [times_DEF;Neg_DEF;abs_DEF] THEN REPEAT STRIP_TAC THENL
     [REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
      REWRITE_TAC [NOT_SUC;MULT_CLAUSES];
      REWRITE_TAC [Int_11] THEN 
      SUBST1_TAC (SPECL ["SUC n";"m:num"] MULT_SYM) THEN REFL_TAC;
      REWRITE_TAC [NOT_EQ_SYM(SPEC_ALL(int_constr_distinct))]]);;

% Prove that "neg" is the same as multiplication by minus one.		%
let neg_times_THM = 
    prove_thm
    (`neg_times_THM`,
     "!i. neg i = (Nint 0) times i",
     INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC THEN
     REWRITE_TAC [neg_DEF;times_THM;MULT_CLAUSES;ADD_CLAUSES] THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THENL
     [REWRITE_TAC [NOT_LESS_0];
      REWRITE_TAC [LESS_0;NOT_SUC]]);;



% Prove that multiplication is commutative.				%
let times_COMM = 
    prove_thm
    (`times_COMM`,
     "!i j. i times j = j times i",
     REPEAT ((INDUCT_THEN int_Induct ASSUME_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [times_THM;Int_11] THEN
     MATCH_ACCEPT_TAC MULT_SYM);;

% Prove that Int 1 is the identity.					%
let times_ID = 
    prove_thm
    (`times_ID`,
     "!i. (i times (Int 1) = i) /\ ((Int 1) times i = i)",
     INDUCT_THEN int_Induct ASSUME_TAC THEN
     REWRITE_TAC [times_THM;num_CONV "1";MULT_CLAUSES;PRE;NOT_SUC]);;

% prove that n * 0 = 0.							%
let times_0 = 
    prove_thm
    (`times_0`,
     "!i. (i times (Int 0) = (Int 0)) /\ ((Int 0) times i = (Int 0))",
     INDUCT_THEN int_Induct ASSUME_TAC THEN
     REWRITE_TAC [times_THM;num_CONV "1";MULT_CLAUSES]);;

let Nint_EQ_Nint0_TIMES = 
    prove_thm
    (`Nint_EQ_Nint0_TIMES`,
% ?? "!n. ?n'. (Nint n) = ((Nint 0) times (Int (SUC n)))", %
     "!n. (Nint n) = ((Nint 0) times (Int (SUC n)))",
     REWRITE_TAC [times_THM;NOT_SUC;MULT_CLAUSES;ADD_CLAUSES;PRE]);;

% Prove that times is associative.  Done by cases.			%

% + + + case								%
let times_assoc_lemma1 = 
    TAC_PROOF
    (([], "!n m p. (Int n) times ((Int m) times (Int p)) = 
		  ((Int n) times (Int m)) times (Int p)"),
     REWRITE_TAC [times_THM;MULT_ASSOC]);;

% + + - case								%
let times_assoc_lemma2 = 
    TAC_PROOF
    (([], "!n m p. (Int n) times ((Int m) times (Nint p)) = 
		  ((Int n) times (Int m)) times (Nint p)"),
     PURE_REWRITE_TAC [times_THM] THEN REPEAT GEN_TAC THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "m:num" num_CASES) THEN
     REWRITE_TAC [times_0;NOT_SUC;MULT_CLAUSES;times_THM] THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
     REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;NOT_SUC;Nint_11;PRE] THEN
     let thl =  [LEFT_ADD_DISTRIB;ADD_ASSOC;MULT_ASSOC;RIGHT_ADD_DISTRIB] in
     let th = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ in
     REWRITE_TAC (EQ_MONO_ADD_EQ . thl) THEN
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th] THEN
     CONV_TAC (RAND_CONV (REWRITE_CONV ADD_SYM)) THEN
     REWRITE_TAC [EQ_MONO_ADD_EQ;ADD_ASSOC] THEN
     MATCH_ACCEPT_TAC ADD_SYM);;

% - - + case								%
let times_assoc_lemma3 = 
    TAC_PROOF
    (([], "!n m p. (Nint n) times ((Nint m) times (Int p)) = 
		  ((Nint n) times (Nint m)) times (Int p)"),
     PURE_REWRITE_TAC [times_THM] THEN REPEAT GEN_TAC THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "p:num" num_CASES) THEN
     REWRITE_TAC [times_0;NOT_SUC;MULT_CLAUSES;times_THM] THEN
     REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;Int_11;PRE] THEN
     let thl =  [LEFT_ADD_DISTRIB;ADD_ASSOC;MULT_ASSOC;RIGHT_ADD_DISTRIB] in
     REWRITE_TAC (INV_SUC_EQ . thl) THEN
     SUBST1_TAC (SPECL ["m:num";"n':num"] MULT_SYM) THEN
     let th = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ in
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th] THEN
     CONV_TAC(RAND_CONV(RAND_CONV(REWRITE_CONV ADD_SYM))) THEN
     SUBST1_TAC (SPECL ["n'*m";"n':num"] ADD_SYM) THEN
     REWRITE_TAC [ADD_ASSOC;EQ_MONO_ADD_EQ] THEN
     CONV_TAC (RATOR_CONV(RAND_CONV(REWRITE_CONV ADD_SYM))) THEN
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th] THEN
     REWRITE_TAC [SYM(SPEC_ALL MULT_ASSOC)] THEN     
     SUBST1_TAC (SPECL ["n':num";"m:num"] MULT_SYM) THEN
     REFL_TAC);;
     
% - - - case								%
let times_assoc_lemma4 = 
    TAC_PROOF
    (([], "!n m p. (Nint n) times ((Nint m) times (Nint p)) = 
		  ((Nint n) times (Nint m)) times (Nint p)"),
     PURE_REWRITE_TAC [times_THM] THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;NOT_SUC;PRE;Nint_11] THEN
     SUBST1_TAC (SPECL ["n:num";"m:num"] MULT_SYM) THEN
     let thl =  [LEFT_ADD_DISTRIB;ADD_ASSOC;MULT_ASSOC;RIGHT_ADD_DISTRIB] in
     let th = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ in
     REWRITE_TAC thl THEN
     CONV_TAC (RATOR_CONV(RAND_CONV(REWRITE_CONV ADD_SYM))) THEN
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th] THEN
     CONV_TAC (RAND_CONV(REWRITE_CONV ADD_SYM)) THEN 
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th] THEN
     SUBST1_TAC (SPECL ["p:num";"n:num"] MULT_SYM) THEN
     CONV_TAC (RAND_CONV(REWRITE_CONV ADD_SYM)) THEN 
     REWRITE_TAC (EQ_MONO_ADD_EQ . thl) THEN
     CONV_TAC (RATOR_CONV(RAND_CONV(REWRITE_CONV ADD_SYM))) THEN      
     REWRITE_TAC (EQ_MONO_ADD_EQ . thl) THEN
     REWRITE_TAC [SYM(SPEC_ALL MULT_ASSOC)] THEN     
     SUBST1_TAC (SPECL ["p:num";"n:num"] MULT_SYM) THEN
     REFL_TAC);;

let times_ASSOC = 
    prove_thm
    (`times_ASSOC`,
     "!i j k. i times (j times k) = (i times j) times k",
      REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THENL
      [MATCH_ACCEPT_TAC times_assoc_lemma1;
       MATCH_ACCEPT_TAC times_assoc_lemma2;
       PURE_ONCE_REWRITE_TAC [SPEC "Nint n" times_COMM] THEN
       PURE_ONCE_REWRITE_TAC [times_assoc_lemma2] THEN
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Int n"] times_COMM] THEN
       REWRITE_TAC [times_assoc_lemma2];
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] times_COMM] THEN
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] times_COMM] THEN
       PURE_ONCE_REWRITE_TAC [times_assoc_lemma3] THEN 
       SUBST1_TAC (SPECL ["Nint n'";"Nint n''"] times_COMM) THEN
       MATCH_ACCEPT_TAC times_COMM;
       PURE_ONCE_REWRITE_TAC [SPEC "Nint n" times_COMM] THEN
       SUBST1_TAC (SPECL ["Int n'";"Int n''"] times_COMM) THEN
       REWRITE_TAC [SYM(SPEC_ALL times_assoc_lemma2)] THEN
       MATCH_ACCEPT_TAC times_COMM;
       PURE_ONCE_REWRITE_TAC [SPECL ["i:int";"Nint n"] times_COMM] THEN
       REWRITE_TAC [times_assoc_lemma3] THEN
       SUBST1_TAC (SPECL ["Nint n";"Nint n''"] times_COMM) THEN
       REFL_TAC;
       MATCH_ACCEPT_TAC times_assoc_lemma3;
       MATCH_ACCEPT_TAC times_assoc_lemma4]);; 

% Do plus distrib by cases...						%

% x + + case								%
let dist_lemma1 =  
    TAC_PROOF
    (([], "!i n m. i times ((Int n) plus (Int m)) = 
		   (i times (Int n)) plus (i times (Int m))"),
    INDUCT_THEN int_Induct (K ALL_TAC) THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC [plus_THM;times_THM;LEFT_ADD_DISTRIB];
%was STRIP_THM_THEN SUBST1_TAC  (SPEC "n:num" Nint_EQ_Nint0_TIMES) THEN %
     ONCE_REWRITE_TAC [(SPEC "n:num" Nint_EQ_Nint0_TIMES)] THEN
     REWRITE_TAC [SYM(SPEC_ALL times_ASSOC)] THEN
     REWRITE_TAC [SYM(SPEC_ALL neg_times_THM)] THEN
     REWRITE_TAC [plus_THM;times_THM;LEFT_ADD_DISTRIB;neg_DEF] THEN
     REWRITE_TAC [plus_THM;neg_DEF] THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n':num" num_CASES) THEN
     REWRITE_TAC [plus_THM;ADD_CLAUSES;MULT_CLAUSES;LESS_REFL;plus_ID] THEN
     REWRITE_TAC [LESS_0;PRE] THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "m:num" num_CASES) THEN
     REWRITE_TAC [plus_THM;ADD_CLAUSES;MULT_CLAUSES;NOT_LESS_0;SUB_0] THEN
     REWRITE_TAC [LESS_0;PRE;ADD_CLAUSES;plus_THM]]);;

% x - - case								%
let dist_lemma2 = 
    TAC_PROOF
    (([], "!i n m. i times ((Nint n) plus (Nint m)) = 
		   (i times (Nint n)) plus (i times (Nint m))"),
    INDUCT_THEN int_Induct (K ALL_TAC) THEN REPEAT GEN_TAC THENL
    [REWRITE_TAC [plus_THM;times_THM] THEN
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN    
     REWRITE_TAC [plus_ID;ADD_CLAUSES;NOT_SUC] THEN
     REWRITE_TAC [plus_THM;Nint_11;ADD_CLAUSES;MULT_CLAUSES;PRE] THEN
     REWRITE_TAC [INV_SUC_EQ;ADD_ASSOC;EQ_MONO_ADD_EQ] THEN
     CONV_TAC (RAND_CONV(RATOR_CONV(RAND_CONV(REWRITE_CONV ADD_SYM)))) THEN
     let th = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ in
     REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);th;LEFT_ADD_DISTRIB] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     REWRITE_TAC [plus_THM;times_THM;Int_11] THEN
     PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL LEFT_ADD_DISTRIB)] THEN
     PURE_ONCE_REWRITE_TAC [MULT_SYM] THEN
     PURE_ONCE_REWRITE_TAC [MULT_SUC_EQ] THEN
     REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES]]);;


% + + - case								%
let dist_lemma3 = 
    TAC_PROOF
    (([], "!p n m. (Int p) times ((Int n) plus (Nint m)) = 
		   ((Int p) times (Int n)) plus ((Int p) times (Nint m))"),
    REPEAT GEN_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "p:num" num_CASES) THENL
    [REWRITE_TAC [times_0;plus_ID];
     REWRITE_TAC [plus_THM;times_THM;NOT_SUC] THEN
     PURE_ONCE_REWRITE_TAC [el 6 (CONJUNCTS (SPEC_ALL MULT_CLAUSES))] THEN
     REWRITE_TAC [ADD_CLAUSES;PRE] THEN
     ASM_CASES_TAC "m < n" THEN ASM_REWRITE_TAC [SYM(SPEC_ALL SUB_PLUS)] THENL
     [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [ADD_CLAUSES;num_CONV "1"] THEN
      PURE_ONCE_REWRITE_TAC [el 6 (CONJUNCTS (SPEC_ALL MULT_CLAUSES))] THEN
      REWRITE_TAC [ADD_CLAUSES;LESS_THM] THEN
      let th1 = PURE_ONCE_REWRITE_RULE [ADD_SYM] EQ_MONO_ADD_EQ in
      let th2 = PURE_ONCE_REWRITE_RULE [ADD_SYM] LESS_MONO_ADD_EQ in
      REWRITE_TAC [th1;th2;MULT_MONO_EQ;LESS_MULT_MONO] THEN
      PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
      REWRITE_TAC [SYM(SPEC_ALL LESS_OR_EQ);LESS_EQ_ADD] THEN
      REWRITE_TAC [times_THM;Int_11] THEN
      SUBST1_TAC (SPECL ["m:num";"p:num"] ADD_SYM) THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 4 (CONJUNCTS ADD_CLAUSES))] THEN
      REWRITE_TAC [SUB_PLUS;ADD_SUB] THEN
      PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [ADD_SUB;SUB_MONO_EQ] THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB] THEN REWRITE_TAC [ADD_SUB];
      POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LESS_OR_EQ;NOT_LESS]) THENL
      [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
       PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
       PURE_ONCE_REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
       let th1 = REWRITE_RULE [ADD_CLAUSES]
                   (SPECL["m:num";"0"]LESS_MONO_ADD_EQ) in
       let th2 = PURE_ONCE_REWRITE_RULE [ADD_SYM] th1 in
       REWRITE_TAC [th2;SYM(SPEC_ALL ADD_ASSOC);NOT_LESS_0] THEN
       REWRITE_TAC [times_THM;Nint_11;NOT_SUC] THEN
       PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [ADD_SUB] THEN
       PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN 
       REWRITE_TAC [ADD_SUB;ADD_ASSOC] THEN
       REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;PRE;ADD_ASSOC];
       let th1 = REWRITE_RULE [ADD_CLAUSES]
                   (SPECL["m:num";"0"]LESS_MONO_ADD_EQ) in
       ASM_REWRITE_TAC [SUB_EQUAL_0;th1;NOT_LESS_0] THEN
       REWRITE_TAC [times_THM;NOT_SUC;Nint_11] THEN      
       REWRITE_TAC [ADD_SUB] THEN
       REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES;PRE]]]]);;

% - + - case								%
let dist_lemma4 = 
    TAC_PROOF
    (([], "!p n m. (Nint p) times ((Nint n) plus (Int m)) = 
		   ((Nint p) times (Nint n)) plus ((Nint p) times (Int m))"),
    REPEAT GEN_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "m:num" num_CASES) THENL
    [REWRITE_TAC [times_0;plus_ID];
     REWRITE_TAC [plus_THM;times_THM;NOT_SUC] THEN
     ASM_CASES_TAC "n < SUC n'" THEN ASM_REWRITE_TAC [] THENL
     [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      PURE_REWRITE_TAC [ADD_ASSOC] THEN 
      SUBST1_TAC (SPECL ["n:num";"p':num"] ADD_SYM) THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);SYM(SPEC_ALL SUB_PLUS)] THEN
      REWRITE_TAC [ADD_SUB] THEN
      PURE_ONCE_REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
      SUBST1_TAC (SYM(SPEC "n:num" ADD1)) THEN
      SUBST1_TAC (SPECL ["SUC n";"SUC p"] MULT_SYM) THEN
      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "p':num" num_CASES) THENL
      [REWRITE_TAC [times_0;MULT_CLAUSES;ADD_CLAUSES;PRE;LESS_SUC_REFL] THEN
       REWRITE_TAC [num_CONV "1";SUB_MONO_EQ;SUB_EQUAL_0;ADD_CLAUSES];
       SUBST1_TAC(el 6(CONJUNCTS (SPECL["SUC n'";"p:num"] MULT_CLAUSES))) THEN
       let th1 = REWRITE_RULE [ADD_CLAUSES]
			     (SPECL["m:num";"0"] LESS_MONO_ADD_EQ) in
       REWRITE_TAC [ADD_CLAUSES;th1;PRE;NOT_LESS_0;ADD_SUB] THEN
       REWRITE_TAC [times_THM;NOT_SUC;Nint_11] THEN
       REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;PRE;ADD_ASSOC]];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LESS]) THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [SYM(SPEC_ALL LESS_EQ)]) THEN
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
      REWRITE_TAC [num_CONV "1";ADD_CLAUSES;SUB_MONO_EQ] THEN
      SUBST1_TAC (SPECL ["n':num";"p':num"] ADD_SYM) THEN
      REWRITE_TAC [ADD_SUB] THEN 
      SUBST1_TAC (SPECL ["SUC n'";"SUC p"] MULT_SYM) THEN
      SUBST1_TAC(el 6(CONJUNCTS (SPECL["SUC p";"n':num"] MULT_CLAUSES))) THEN
      REWRITE_TAC [ADD_CLAUSES;PRE] THEN
      PURE_REWRITE_TAC [el 6 (CONJUNCTS (SPEC_ALL MULT_CLAUSES))] THEN
      PURE_ONCE_REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC [ADD_ASSOC;LESS_MONO_ADD_EQ] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 4 (CONJUNCTS ADD_CLAUSES))] THEN
      REWRITE_TAC [LESS_ADD_SUC;times_THM] THEN
      REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES;Int_11;SYM(SPEC_ALL SUB_PLUS)]THEN
      REWRITE_TAC [SUB_MONO_EQ] THEN PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
      PURE_ONCE_REWRITE_TAC [SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN
      PURE_REWRITE_TAC 
            [SPECL ["p*p'";"p':num";"((p * n) + x)"] ADD_ASSOC] THEN
      REWRITE_TAC [SPEC "SUC n" ADD_ASSOC;ADD_SUB] THEN
      CONV_TAC (RAND_CONV (REWRITE_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_CLAUSES;ADD_ASSOC]]]);;


let LEFT_plus_DISTRIB = 
    prove_thm
    (`LEFT_plus_DISTRIB`,
     "!i j k. i times (j plus k) = (i times j) plus (i times k)",
     REPEAT ((INDUCT_THEN int_Induct ASSUME_TAC) THEN GEN_TAC) THENL     
     [MATCH_ACCEPT_TAC dist_lemma1;
      MATCH_ACCEPT_TAC dist_lemma3;
      PURE_ONCE_REWRITE_TAC [plus_COMM] THEN MATCH_ACCEPT_TAC dist_lemma3;
      MATCH_ACCEPT_TAC dist_lemma2;
      MATCH_ACCEPT_TAC dist_lemma1;
      PURE_ONCE_REWRITE_TAC [plus_COMM] THEN MATCH_ACCEPT_TAC dist_lemma4;
      MATCH_ACCEPT_TAC dist_lemma4;
      MATCH_ACCEPT_TAC dist_lemma2]);;

let RIGHT_plus_DISTRIB = 
    prove_thm
    (`RIGHT_plus_DISTRIB`,
     "!i j k. (j plus k) times i = (j times i) plus (k times i)",
     PURE_ONCE_REWRITE_TAC [times_COMM] THEN REPEAT GEN_TAC THEN
     MATCH_ACCEPT_TAC LEFT_plus_DISTRIB);;

let neg_DISTRIB = 
    prove_thm
    (`neg_DISTRIB`,
     "!i j. neg(i plus j) = (neg i) plus (neg j)",
     REWRITE_TAC [neg_times_THM;LEFT_plus_DISTRIB]);;

let minus_DEF = 
     new_infix_definition
     (`minus_DEF`, "minus i j = i plus (neg j)");;

let int_LESS_DEF = 
     new_infix_definition
     (`int_LESS_DEF`, "<< i j = Pos(j minus i)");;

let int_LESS_EQ_DEF = 
     new_infix_definition
     (`int_LESS_EQ_DEF`, "Leq i j = ((i << j) \/ (i = j))");;

% note: INDUCT_THEN bug shows up here. Not any more in HOL88 ?%
let int_TRICHOTOMY = 
    prove_thm
    (`int_TRICHOTOMY`,
     "!i. Pos i \/ Neg i \/ (i = Int 0)",
     INDUCT_THEN int_Induct (K ALL_TAC) THEN
     REWRITE_TAC [Pos_DEF;Neg_DEF] THEN GEN_TAC THEN 
     STRIP_ASSUME_TAC (SPEC "n:num" LESS_0_CASES) THEN
     ASM_REWRITE_TAC[]);;

let minus_EQ_0 = 
    prove_thm
    (`minus_EQ_0`,
     "!i j. ((i minus j) = Int 0) = (i = j)",
     REWRITE_TAC [minus_DEF] THEN REPEAT GEN_TAC THEN
     let th = SPECL ["j:int";"i plus (neg j)";"Int 0"] RIGHT_plus_CANCEL in
     SUBST1_TAC (SYM th) THEN REWRITE_TAC [plus_ID] THEN
     REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC);plus_INV;plus_ID]);;

let Neg_Pos_neg = 
    prove_thm
    (`Neg_Pos_neg`,
     "!i. Neg i = Pos (neg i)",
     INDUCT_THEN int_Induct (K ALL_TAC) THEN
     REWRITE_TAC [Neg_DEF;Pos_DEF;neg_DEF;LESS_0] THEN
     GEN_TAC THEN ASM_CASES_TAC "0 < n" THEN 
     ASM_REWRITE_TAC [Pos_DEF;LESS_REFL]);;

let Pos_plus_CLOSURE = 
    prove_thm
    (`Pos_plus_CLOSURE`,
     "!i j. ((Pos i) /\ (Pos j)) ==> (Pos (i plus j))",
     REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [Pos_DEF;plus_THM] THEN
     REPEAT STRIP_TAC THEN 
     POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [LESS_0;ADD_CLAUSES;num_CONV "1"]);;

let int_less_CASES = 
    prove_thm
    (`int_less_CASES`,
     "!j i. (i << j) \/ (j << i) \/ (i = j)",
     REPEAT GEN_TAC THEN REWRITE_TAC [int_LESS_DEF] THEN
     SUBST1_TAC (SYM(SPECL ["i:int";"j:int"] minus_EQ_0)) THEN
     PURE_ONCE_REWRITE_TAC [minus_DEF] THEN
     let th = (SYM(SPECL ["neg j";"i:int"] neg_DISTRIB)) in
     SUBST1_TAC (REWRITE_RULE [neg_neg_THM] th) THEN
     SUBST1_TAC (SPECL ["neg j";"i:int"] plus_COMM) THEN
     REWRITE_TAC [SYM(SPEC_ALL Neg_Pos_neg)] THEN
     STRIP_ASSUME_TAC (SPEC "i plus (neg j)" int_TRICHOTOMY) THEN
     ASM_REWRITE_TAC []);;

let lemma = 
    TAC_PROOF
    (([], "!i j k. (k minus i) = ((k minus j) plus (j minus i))"),
     REWRITE_TAC [minus_DEF;plus_ASSOC] THEN
     PURE_ONCE_REWRITE_TAC [plus_COMM] THEN
     REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC);plus_INV;plus_ID]);;

let int_less_TRANS = 
    prove_thm
    (`int_less_TRANS`,
     "!i j k. ((i << j) /\ (j << k)) ==> (i << k)",
     REWRITE_TAC [int_LESS_DEF] THEN REPEAT STRIP_TAC THEN
     SUBST1_TAC (SPECL ["i:int";"j:int";"k:int"] lemma) THEN
     MATCH_MP_TAC Pos_plus_CLOSURE THEN ASM_REWRITE_TAC[]);;

let int_LESS_plus_MONO = 
    prove_thm
    (`int_LESS_plus_MONO`,
     "!i j k. ((i plus k) << (j plus k)) = (i << j)",
     PURE_REWRITE_TAC [int_LESS_DEF] THEN
     REWRITE_TAC [minus_DEF;neg_DISTRIB] THEN REPEAT GEN_TAC THEN
     SUBST1_TAC (SPECL ["neg i";"neg k"] plus_COMM) THEN
     REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC)] THEN
     SUBST1_TAC (SPECL ["k:int";"neg k";"neg i"] plus_ASSOC) THEN
     REWRITE_TAC [plus_INV;plus_ID]);;



let int_LESS_minus_MONO = 
    prove_thm
    (`int_LESS_minus_MONO`,
     "!i j k. ((k minus j) << (k minus i)) = (i << j)",
     PURE_REWRITE_TAC [int_LESS_DEF] THEN
     REWRITE_TAC [minus_DEF;neg_DISTRIB;neg_neg_THM] THEN 
     REPEAT GEN_TAC THEN
     SUBST1_TAC (SPECL ["k:int";"neg i"] plus_COMM) THEN
     REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC)] THEN
     SUBST1_TAC (SPECL ["k:int";"neg k";"j:int"] plus_ASSOC) THEN
     REWRITE_TAC [plus_INV;plus_ID] THEN
     SUBST1_TAC (SPECL ["neg i";"j:int"] plus_COMM) THEN REFL_TAC);;

let neg_THM = 
    prove_thm
    (`neg_THM`,
     "(neg (Int 0) = (Int 0)) /\
      (!n. neg(Int(SUC n)) = Nint n) /\
      (!n. neg(Nint n) = Int(SUC n))",
     REWRITE_TAC [neg_DEF;LESS_REFL;PRE;LESS_0]);;


let Pos_times_CLOSURE = 
    prove_thm
    (`Pos_times_CLOSURE`,
     "!i j. ((Pos i) /\ (Pos j)) ==> (Pos (i times j))",
     REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [Pos_DEF;times_THM] THEN REPEAT STRIP_TAC THEN 
     POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [LESS_0;ADD_CLAUSES;num_CONV "1";MULT_CLAUSES]);;

let int_LESS_times = 
    prove_thm
    (`int_LESS_times`,
     "!i j k. (Int 0 << k) ==> ((j << i) ==> ((k times j) << (k times i)))",
     PURE_REWRITE_TAC [int_LESS_DEF] THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [minus_DEF;neg_THM;plus_ID;neg_times_THM] THEN 
     REWRITE_TAC [times_ASSOC] THEN
     SUBST1_TAC (SPECL ["Nint 0";"k:int"] times_COMM) THEN
     REWRITE_TAC [SYM(SPEC_ALL times_ASSOC);
		  SYM(SPEC_ALL LEFT_plus_DISTRIB)] THEN
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC Pos_times_CLOSURE THEN ASM_REWRITE_TAC[]);;

let Int_less_num_less = 
    prove_thm
    (`Int_less_num_less`,
     "!n m. (Int n << Int m) = (n < m)",
     REPEAT STRIP_TAC THEN 
     REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
     REWRITE_TAC[int_LESS_DEF;minus_DEF;neg_THM;plus_THM;Neg_DEF;abs_DEF]THENL
     [REWRITE_TAC [ADD_CLAUSES;Pos_DEF];
      ASM_CASES_TAC "n' < m" THEN ASM_REWRITE_TAC [Pos_DEF] THENL
      [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
       SUBST1_TAC (SPECL ["n':num";"p+1"] ADD_SYM) THEN
       REWRITE_TAC [ADD_SUB] THEN
       REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "p:num" num_CASES) THEN
       REWRITE_TAC [LESS_REFL;ADD_CLAUSES;LESS_MONO_EQ;num_CONV "1"] THEN
       REWRITE_TAC [LESS_0;SYM(el 3 (CONJUNCTS ADD_CLAUSES))] THEN 
       PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC LESS_ADD_SUC;
       POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_LESS] THEN
       REWRITE_TAC [LESS_OR_EQ] THEN REPEAT STRIP_TAC THENL
       [IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC [LESS_SUC_REFL]]]]);;

let Nint_less_Int = 
    prove_thm
    (`Nint_less_Int`,
     "!n m. Nint n << Int m",
     REWRITE_TAC [int_LESS_DEF;minus_DEF;neg_THM] THEN
     REWRITE_TAC [plus_THM;ADD_CLAUSES;Pos_DEF;LESS_0]);;
      
let int_LESS_plus_1 = 
    prove_thm
    (`int_LESS_plus_1`,
     "!i j. i << j ==> ?n. j = ((Int (n + 1)) plus i)",
     REWRITE_TAC [int_LESS_DEF;minus_DEF] THEN
     INDUCT_THEN int_Induct (K ALL_TAC) THENL
     [GEN_TAC THEN 
      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THENL
      [REWRITE_TAC [neg_THM;plus_ID] THEN
       INDUCT_THEN int_Induct (K ALL_TAC) THEN REWRITE_TAC [Pos_DEF] THEN
       GEN_TAC THEN 
       DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
       EXISTS_TAC "p:num" THEN REWRITE_TAC [ADD_CLAUSES];
       REWRITE_TAC [neg_THM] THEN INDUCT_THEN int_Induct (K ALL_TAC) THEN
       REWRITE_TAC [Pos_DEF;plus_THM] THEN GEN_TAC THEN
       ASM_CASES_TAC "n' < n" THEN ASM_REWRITE_TAC [Pos_DEF] THEN
       POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
       SUBST1_TAC (SPECL ["n':num";"p+1"] ADD_SYM) THEN
       REWRITE_TAC [ADD_SUB;Int_11] THEN
       DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
       EXISTS_TAC "p':num" THEN REWRITE_TAC [ADD_CLAUSES;num_CONV "1"]];
      REWRITE_TAC [neg_THM] THEN GEN_TAC THEN
      INDUCT_THEN int_Induct (K ALL_TAC) THENL
      [REWRITE_TAC [plus_THM;Pos_DEF;ADD_CLAUSES;LESS_0] THEN
       GEN_TAC THEN EXISTS_TAC "n' + n" THEN
       REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);SYM(SPEC_ALL SUB_PLUS)] THEN
       REWRITE_TAC [ADD_SUB] THEN REWRITE_TAC [ADD_ASSOC] THEN
       SUBST1_TAC (SPECL ["n':num";"n:num"] ADD_SYM) THEN
       REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC);num_CONV "1"] THEN
       PURE_ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
       REWRITE_TAC [LESS_ADD_SUC];
       REWRITE_TAC [plus_THM;Pos_DEF;ADD_CLAUSES;LESS_0] THEN 
       GEN_TAC THEN
       ASM_CASES_TAC "n' < (SUC n)" THEN ASM_REWRITE_TAC [Pos_DEF] THEN
       REWRITE_TAC [SYM(SPEC_ALL SUB_PLUS);SUB_MONO_EQ;SYM(SPEC_ALL ADD1)]THEN
       REWRITE_TAC [SYM(SPEC_ALL SUB_LESS_0)] THEN
       DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
       EXISTS_TAC "p:num" THEN REWRITE_TAC [ADD_CLAUSES;num_CONV "1"] THEN
       REWRITE_TAC [SUB_MONO_EQ;ADD_SUB;LESS_MONO_EQ] THEN
       REWRITE_TAC [LESS_EQ] THEN
       ASSUME_TAC (SPECL ["p:num";"n':num"] LESS_ADD_SUC) THEN
       POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [ADD_CLAUSES])) THEN
       SUBST1_TAC (SPECL ["n':num";"p:num"] ADD_SYM) THEN
       IMP_RES_TAC LESS_EQ_ANTISYM THEN
       ASM_CASES_TAC "SUC(p+n')<=p" THEN RES_TAC THEN
       ASM_REWRITE_TAC []]]);;

let Nint_less_num_less = 
    prove_thm
    (`Nint_less_num_less`,
     "!n m. (Nint n << Nint m) = (m < n)",
     REPEAT STRIP_TAC THEN 
     REWRITE_TAC [int_LESS_DEF;minus_DEF;neg_THM;plus_THM;LESS_THM] THEN
     PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
     REWRITE_TAC [SYM(SPEC_ALL LESS_OR_EQ)] THEN
     STRIP_ASSUME_TAC (SPECL ["n:num";"m:num"] LESS_CASES) THENL
     [ASM_REWRITE_TAC[GEN_ALL(SYM(SPEC_ALL NOT_LESS));Pos_DEF] THEN
      ASM_REWRITE_TAC [NOT_LESS;LESS_OR_EQ];
      ASM_REWRITE_TAC[Pos_DEF] THEN
      REWRITE_TAC [num_CONV "1";SYM(SPEC_ALL SUB_PLUS)] THEN
      REWRITE_TAC [ADD_CLAUSES;SUB_MONO_EQ] THEN
      REWRITE_TAC [SYM(SPEC_ALL SUB_LESS_0)]]);;

let lemma = 
    CONJ (NOT_EQ_SYM(SPEC_ALL int_constr_distinct)) int_constr_distinct;;

let lemma2 = 
    let th = TAC_PROOF(([], "0 < ((SUC n) * (SUC m))"),
    			REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;LESS_0]) in
    let th' = SPECL ["(SUC n) * (SUC m)";"(SUC n') * (SUC m')"] INV_PRE_EQ in
    REWRITE_RULE [th] th';;

let LEFT_times_CANCEL = 
    prove_thm
    (`LEFT_times_CANCEL`,
     "!k i j. (~(k = Int 0)) ==> ((k times i = k times j) = (i = j))",
     let th = PURE_ONCE_REWRITE_RULE [MULT_SYM] MULT_SUC_EQ in
     REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THEN
     REWRITE_TAC [times_THM;Int_11;Nint_11;lemma] THENL
     [REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
      REWRITE_TAC [th];
      STRIP_TAC THEN ASM_REWRITE_TAC [lemma];
      STRIP_TAC THEN ASM_REWRITE_TAC [lemma];
      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n:num" num_CASES) THEN
      REWRITE_TAC [Nint_11;NOT_SUC;lemma2;th;INV_SUC_EQ];
      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n':num" num_CASES) THEN
      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC (SPEC "n'':num" num_CASES) THEN
      REWRITE_TAC [Nint_11;NOT_SUC;NOT_EQ_SYM(SPEC_ALL NOT_SUC);lemma] THEN
      REWRITE_TAC [lemma2;MULT_SUC_EQ];
      ASM_CASES_TAC "n' = 0" THEN 
      ASM_REWRITE_TAC [lemma;Int_11;NOT_EQ_SYM(SPEC_ALL NOT_SUC);
			MULT_CLAUSES;ADD_CLAUSES];
      ASM_CASES_TAC "n'' = 0" THEN 
      ASM_REWRITE_TAC [lemma;Int_11;NOT_SUC;MULT_CLAUSES;ADD_CLAUSES];
      REWRITE_TAC [th;INV_SUC_EQ]]);;

let RIGHT_times_CANCEL = 
    save_thm
    (`RIGHT_times_CANCEL`,
     PURE_ONCE_REWRITE_RULE [times_COMM] LEFT_times_CANCEL);;

let int_times_2 = 
    prove_thm
    (`int_times_2`,
     "!i. ((Int 2) times i) = (i plus i)",
     CONV_TAC (DEPTH_CONV num_CONV) THEN
     INDUCT_THEN int_Induct (K ALL_TAC) THEN
     REWRITE_TAC [times_THM;MULT_CLAUSES;ADD_CLAUSES] THENL
     [REWRITE_TAC [plus_THM];
      REWRITE_TAC [NOT_SUC;plus_THM;PRE]]);;

let NOT_int_EVEN_EQ_ODD = 
    prove_thm
    (`NOT_int_EVEN_EQ_ODD`,
     "!i j. ~((i plus i) = ((j plus j) plus (Int 1)))",
     REPEAT (INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC) THEN 
     REWRITE_TAC 
       [plus_THM;num_CONV "1";ADD_CLAUSES;LESS_MONO_EQ;NOT_LESS_0] THENL
     [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [Int_11] THEN MATCH_ACCEPT_TAC NOT_ODD_EQ_EVEN;
      REWRITE_TAC [int_constr_distinct];
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [int_constr_distinct];
      REWRITE_TAC [Nint_11;SUB_MONO_EQ;SUB_0;NOT_ODD_EQ_EVEN]]);;


let lemma = 
    TAC_PROOF(([], "!n. (0 < n) = (~(n = 0))"),
    	      GEN_TAC THEN 
	      REPEAT_TCL STRIP_THM_THEN SUBST1_TAC 
                      (SPEC "n:num" num_CASES) THEN
	      REWRITE_TAC [LESS_REFL;LESS_0;NOT_SUC]);;

% Da for integers.							%
let int_Da = 
    prove_thm 
    (`int_Da`,
     "!k n. ((Int 0) << (Int n)) ==>
      ?q r. (k = (q times (Int n)) plus r)/\((Int 0) Leq r)/\(r << (Int n))",
     REWRITE_TAC [Int_less_num_less;lemma] THEN
     INDUCT_THEN int_Induct (K ALL_TAC) THENL
     [REPEAT STRIP_TAC THEN
      IMP_RES_TAC (SPEC "n:num" Da) THEN 
      POP_ASSUM (STRIP_ASSUME_TAC o SPEC "n:num") THEN
      MAP_EVERY EXISTS_TAC ["Int q";"Int r"] THEN
      ASM_REWRITE_TAC [Int_11;times_THM;plus_THM;int_LESS_EQ_DEF] THEN
      ASM_REWRITE_TAC [Int_less_num_less] THEN
      PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN 
      MATCH_ACCEPT_TAC LESS_0_CASES;
      REPEAT STRIP_TAC THEN IMP_RES_TAC Da THEN 
      POP_ASSUM (STRIP_ASSUME_TAC o SPEC "n:num") THEN
      ASM_REWRITE_TAC [] THEN 
      MAP_EVERY EXISTS_TAC ["Nint q";"Int (n' - (SUC r))"] THEN
      REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [times_THM;plus_THM] THEN
       POP_ASSUM (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
       REWRITE_TAC [num_CONV "1";ADD_CLAUSES;SUB_MONO_EQ] THEN
       SUBST1_TAC (SPECL ["r:num";"p:num"] ADD_SYM) THEN
       REWRITE_TAC [ADD_SUB] THEN
       PURE_ONCE_REWRITE_TAC [el 6 (CONJUNCTS (SPEC_ALL MULT_CLAUSES))] THEN
       REWRITE_TAC [ADD_CLAUSES;PRE;SYM(SPEC_ALL ADD_ASSOC)] THEN
       (let th = PURE_ONCE_REWRITE_RULE [ADD_SYM]
		 (REWRITE_RULE [ADD_CLAUSES;NOT_LESS_0]
	         (SPECL ["m:num";"0"] LESS_MONO_ADD_EQ)) in
       REWRITE_TAC [th;Nint_11]) THEN
       PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
       REWRITE_TAC [ADD_SUB] THEN
       PURE_ONCE_REWRITE_TAC [SPEC "SUC n" MULT_SYM] THEN
       REWRITE_TAC [MULT_CLAUSES] THEN
       CONV_TAC (RAND_CONV (REWRITE_CONV ADD_SYM)) THEN
       REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
       CONV_TAC (RAND_CONV (REWRITE_CONV ADD_SYM)) THEN
       REWRITE_TAC [ADD_ASSOC];
       REWRITE_TAC [int_LESS_EQ_DEF;Int_11;Int_less_num_less] THEN
       PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN 
       MATCH_ACCEPT_TAC LESS_0_CASES;
       REWRITE_TAC [Int_less_num_less] THEN
       POP_ASSUM (STRIP_THM_THEN SUBST_ALL_TAC o MATCH_MP LESS_ADD_1) THEN
       REWRITE_TAC [num_CONV "1";ADD_CLAUSES;SUB_MONO_EQ] THEN
       SUBST1_TAC (SPECL ["r:num";"p:num"] ADD_SYM) THEN
       REWRITE_TAC [ADD_SUB;SYM(el 4 (CONJUNCTS ADD_CLAUSES))] THEN
       MATCH_ACCEPT_TAC LESS_ADD_SUC]]);;

let int_Quot_Unique = 
    prove_thm
    (`int_Quot_Unique`,
     "!n r1 r2.
      (((Int 0) Leq r1) /\ r1 << (Int n) /\ 
       ((Int 0) Leq r2) /\ r2 << (Int n)) ==>
     (!q1 q2. ((q1 times (Int n)) plus r1 = (q2 times (Int n)) plus r2) ==> 
               (q1 = q2))",
     REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
     STRIP_ASSUME_TAC (SPECL ["q1:int";"q2:int"] int_less_CASES) THENL
     [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
      PURE_ONCE_REWRITE_TAC [plus_COMM] THEN
      REWRITE_TAC [RIGHT_plus_DISTRIB;plus_ASSOC;RIGHT_plus_CANCEL] THEN
      DISCH_THEN (SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC [times_THM;MULT_CLAUSES;num_CONV "1";ADD_CLAUSES] THEN
      REWRITE_TAC [SYM(SPEC_ALL(CONJUNCT1(plus_THM)))] THEN
      (let thm = REWRITE_RULE [plus_ID] 
		 (SPECL ["i:int";"Int 0"] int_LESS_plus_MONO) in
       REWRITE_TAC [plus_ASSOC;thm]) THEN
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [int_LESS_EQ_DEF]) THENL
      [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1);
       POP_ASSUM (SUBST1_TAC o SYM)] THEN
       REWRITE_TAC [plus_THM;Int_less_num_less;NOT_LESS_0];
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
      PURE_ONCE_REWRITE_TAC [plus_COMM] THEN
      REWRITE_TAC [RIGHT_plus_DISTRIB;plus_ASSOC;RIGHT_plus_CANCEL] THEN
      DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC [times_THM;MULT_CLAUSES;num_CONV "1";ADD_CLAUSES] THEN
      REWRITE_TAC [SYM(SPEC_ALL(CONJUNCT1(plus_THM)))] THEN
      (let thm = REWRITE_RULE [plus_ID] 
		 (SPECL ["i:int";"Int 0"] int_LESS_plus_MONO) in
       REWRITE_TAC [plus_ASSOC;thm]) THEN
      REWRITE_TAC [int_LESS_EQ_DEF] THEN
      DISCH_THEN (\th. STRIP_TAC THEN MP_TAC th) THENL
      [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1);
       POP_ASSUM (SUBST1_TAC o SYM)] THEN
       REWRITE_TAC [plus_THM;Int_less_num_less;NOT_LESS_0];
      ASM_REWRITE_TAC[]]);;


let int_Rem_Unique = 
    prove_thm
    (`int_Rem_Unique`,
     "!n r1 r2.
      (((Int 0) Leq r1) /\ r1 << (Int n) /\ 
       ((Int 0) Leq r2) /\ r2 << (Int n)) ==>
     (?q1 q2. (q1 times (Int n)) plus r1 = (q2 times (Int n)) plus r2) ==> 
     (r1 = r2)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC int_Quot_Unique THEN RES_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN POP_ASSUM SUBST_ALL_TAC THEN
     REPEAT 
      (POP_ASSUM (\th. if is_eq (concl th) then MP_TAC th else ALL_TAC)) THEN
     REWRITE_TAC [LEFT_plus_CANCEL]);;

% Define the MODI operator.						%
let MODI = 
    new_infix_definition
    (`MODI`,
     "MODI (k:int) (n:num) =
      @r.?q.(k =((q times (Int n)) plus r)) /\ (Int 0) Leq r /\ r << Int n");;


let Da_MOD_thm = 
    prove_thm
    (`Da_MOD_thm`,
     "!n. (Int 0 << Int n) ==> 
	  !k. ?q. (k = ((q times (Int n)) plus (k MODI n))) /\ 
	  	  (Int 0) Leq (k MODI n) /\
		  ((k MODI n) << (Int n))",
     REPEAT STRIP_TAC THEN
     POP_ASSUM (ASSUME_TAC o MP (SPEC_ALL int_Da)) THEN
     REWRITE_TAC [MODI] THEN
     CONV_TAC SELECT_CONV THEN
     CONV_TAC SWAP_EXISTS_CONV THEN
     POP_ASSUM ACCEPT_TAC);;

let MOD_Less = 
    prove_thm
    (`MOD_Less`,
     "!n. (Int 0) << (Int n) ==> !k. (k MODI n) << (Int n)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL));;

let Leq_MOD = 
    prove_thm
    (`Leq_MOD`,
     "!n. (Int 0) << (Int n) ==> !k. (Int 0) Leq (k MODI n)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL));;

let MOD_One = 
    prove_thm
    (`MOD_One`,
     "!k. (k MODI 1) = Int 0",
     GEN_TAC THEN
     CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
     MP_TAC (SPEC "SUC 0" MOD_Less) THEN
     MP_TAC (SPEC "SUC 0" Leq_MOD) THEN
     REWRITE_TAC [Int_less_num_less;LESS_0;int_LESS_EQ_DEF] THEN
     REPEAT (DISCH_THEN (STRIP_ASSUME_TAC o SPEC_ALL)) THENL
     [POP_ASSUM MP_TAC THEN
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
      REWRITE_TAC [plus_THM;ADD_CLAUSES;num_CONV "1"] THEN
      REWRITE_TAC [Int_less_num_less;LESS_MONO_EQ;NOT_LESS_0];
      ASM_REWRITE_TAC[]]);;

let lemma = 
    TAC_PROOF(
    ([], "!n k. (((Int 0) Leq k) /\ (k << Int n)) ==> (Int 0) << (Int n)"),
    REWRITE_TAC [int_LESS_EQ_DEF] THEN REPEAT STRIP_TAC THENL
    [IMP_RES_TAC (SPECL ["Int 0";"k:int";"Int n"] int_less_TRANS);
     ASM_REWRITE_TAC[]]);;
     

let MOD_ID = 
    prove_thm
    (`MOD_ID`,
     "!n k. ((Int 0) Leq k  /\ k << (Int n)) ==> ((k MODI n) = k)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC lemma THEN 
     IMP_RES_TAC Da_MOD_thm THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
     MP_TAC (SPECL ["n:num";"k MODI n";"k:int"] int_Rem_Unique) THEN 
     UNDISCH_TAC "k = (q times (Int n)) plus (k MODI n)" THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
     POP_ASSUM (\th. ASSUME_TAC (TRANS
        (SUBS [SYM(CONJUNCT2 (SPEC "Int n" times_0))]
              (CONJUNCT2 (SPEC "k:int" plus_ID))) th )) THEN
     POP_ASSUM(ASSUME_TAC o SYM) THEN
     POP_ASSUM(\th. ASSUME_TAC
     (EXISTS ("?q2. (q times (Int n)) plus (k MODI n) = 
                    (q2 times (Int n)) plus k", "Int 0")
            th ) ) THEN
      POP_ASSUM(\th. ASSUME_TAC
      (EXISTS ("?q1. (?q2. (q1 times (Int n)) plus (k MODI n) = 
                    (q2 times (Int n)) plus k)", "q:int")
            th ) ) THEN
      POP_ASSUM(\th. REWRITE_TAC[th]) );;

let Leq_REFL = 
    prove_thm
    (`Leq_REFL`,
     "!i. i Leq i",
     REWRITE_TAC [int_LESS_EQ_DEF]);;

let MOD_EQ_0 = 
    prove_thm
    (`MOD_EQ_0`,
     "!n. (Int 0) << (Int n) ==> !k. ((k times (Int n)) MODI n) = (Int 0)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "k times (Int n)") THEN
     ASSUME_TAC (SPEC "Int 0" Leq_REFL) THEN
     IMP_RES_TAC int_Rem_Unique THEN
     UNDISCH_TAC "!q1 q2.
        ((q1 times (Int n)) plus ((k times (Int n)) MODI n) =
         (q2 times (Int n)) plus (Int 0)) ==>
        ((k times (Int n)) MODI n = Int 0)" THEN DISCH_TAC THEN
     POP_ASSUM ( MP_TAC o SPECL ["q:int";"k:int"] ) THEN
     UNDISCH_TAC "k times (Int n) =
       (q times (Int n)) plus ((k times (Int n)) MODI n)" THEN
     DISCH_TAC THEN POP_ASSUM(\th. REWRITE_TAC[SYM th]) THEN
     REWRITE_TAC[plus_ID]);;

let MOD_Rem_thm = 
    prove_thm
    (`MOD_Rem_thm`,
     "!n k. ((Int 0) Leq k /\ k << (Int n)) ==> 
	     !m. (((m times (Int n)) plus k) MODI n) = k",
     REPEAT STRIP_TAC THEN IMP_RES_TAC lemma THEN
     IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "(m times (Int n)) plus k") THEN
     MP_TAC (SPECL ["n:num";"k:int";
             "(((m times (Int n)) plus k) MODI n)"] int_Rem_Unique) THEN 
     UNDISCH_TAC "(m times (Int n)) plus k =
       (q times (Int n)) plus (((m times (Int n)) plus k) MODI n)" THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
     POP_ASSUM(\th. ASSUME_TAC
       (EXISTS ("?q2. (m times (Int n)) plus k =
       (q2 times (Int n)) plus (((m times (Int n)) plus k) MODI n)","q:int") 
       th)) THEN
     POP_ASSUM(\th. ASSUME_TAC
       (EXISTS ("?q1. ?q2. (q1 times (Int n)) plus k =
       (q2 times (Int n)) plus (((m times (Int n)) plus k) MODI n)","m:int") 
       th)) THEN
     POP_ASSUM(\th. REWRITE_TAC[th]) THEN DISCH_TAC THEN 
     POP_ASSUM(ASSUME_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC);;

let MOD_thm  = 
    prove_thm
    (`MOD_thm`,
     "!n. (Int 0) << (Int n) ==> 
      !k r. (((k times (Int n)) plus r) MODI n) = (r MODI n)",
     REPEAT STRIP_TAC THEN IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "r:int") THEN
     POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (\th. SUBST_OCCS_TAC [[1],th]) THEN
     REWRITE_TAC [plus_ASSOC;SYM(SPEC_ALL RIGHT_plus_DISTRIB)] THEN
     IMP_RES_TAC MOD_Less THEN 
     POP_ASSUM (ASSUME_TAC o SPEC "r:int") THEN
     IMP_RES_TAC Leq_MOD THEN POP_ASSUM (ASSUME_TAC o SPEC "r:int") THEN
     IMP_RES_TAC MOD_Rem_thm THEN ASM_REWRITE_TAC[] );;

let Add_MOD = 
    prove_thm
    (`Add_MOD`,
     "!n. (Int 0) << (Int n) ==>
      !i j.(((i MODI n) plus (j MODI n)) MODI n) = ((i plus j) MODI n)",
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC MOD_thm THEN IMP_RES_TAC Da_MOD_thm THEN
     POP_ASSUM (\th. MAP_EVERY (STRIP_ASSUME_TAC o uncurry SPEC) 
               (["j:int",th;"i:int",th])) THEN 
     POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN 
     POP_ASSUM (\th. SUBST_OCCS_TAC [[2],th]) THEN
     FILTER_ASM_REWRITE_TAC (is_forall) [SYM(SPEC_ALL plus_ASSOC)] THEN
     PURE_ONCE_REWRITE_TAC [plus_COMM] THEN
     POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN 
     POP_ASSUM (\th. SUBST_OCCS_TAC [[2],th]) THEN
     FILTER_ASM_REWRITE_TAC (is_forall) [SYM(SPEC_ALL plus_ASSOC)]);;


let int_Odd_or_Even = 
    prove_thm
    (`int_Odd_or_Even`,
     "!i. ?j. 
      (i = ((Int 2) times j)) \/ (i = ((Int 2) times j) plus (Int 1))",
     INDUCT_THEN int_Induct (K ALL_TAC) THENL
     [INDUCT_TAC THENL
      [EXISTS_TAC "Int 0" THEN REWRITE_TAC [times_0];
       POP_ASSUM STRIP_ASSUME_TAC THENL
       [REWRITE_TAC [ADD1;SYM(SPEC_ALL(CONJUNCT1 plus_THM))] THEN
        EXISTS_TAC "j:int" THEN ASM_REWRITE_TAC [];
        REWRITE_TAC [ADD1;SYM(SPEC_ALL(CONJUNCT1 plus_THM))] THEN
        EXISTS_TAC "(j:int) plus (Int 1)" THEN POP_ASSUM SUBST1_TAC THEN
        REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC);num_CONV "1"] THEN
        REWRITE_TAC [plus_THM;NOT_SUC;ADD_CLAUSES] THEN
        REWRITE_TAC [LEFT_plus_DISTRIB;SYM(REDEPTH_CONV num_CONV "2")] THEN
        REWRITE_TAC [times_ID;SYM(num_CONV "1")]]];
      INDUCT_TAC THENL
      [CONV_TAC (REDEPTH_CONV num_CONV) THEN
       EXISTS_TAC "Nint 0" THEN  
       REWRITE_TAC [times_THM;NOT_SUC;PRE;MULT_CLAUSES;ADD_CLAUSES] THEN
       REWRITE_TAC [plus_THM;LESS_REFL;SUB_EQUAL_0];
       POP_ASSUM STRIP_ASSUME_TAC THENL
       [SUBST1_TAC(SPEC "n:num" (GEN_ALL(SYM(el 2 (CONJUNCTS ADD_CLAUSES))))) THEN
        SUBST1_TAC (SYM(SPECL ["n:num";"0"] (el 4 (CONJUNCTS plus_THM)))) THEN
	POP_ASSUM SUBST1_TAC THEN EXISTS_TAC "(j:int) plus (Nint 0)" THEN 
        REWRITE_TAC [LEFT_plus_DISTRIB;(REDEPTH_CONV num_CONV "2")] THEN
	REWRITE_TAC [times_THM;NOT_SUC;PRE;ADD_CLAUSES;MULT_CLAUSES]THEN
	SUBST1_TAC (num_CONV "1") THEN
	REWRITE_TAC [plus_THM;LESS_REFL;SUB_EQUAL_0;SYM(SPEC_ALL plus_ASSOC)];
        SUBST1_TAC(SPEC "n:num" (GEN_ALL(SYM(el 2 (CONJUNCTS ADD_CLAUSES))))) THEN
        SUBST1_TAC (SYM(SPECL ["n:num";"0"] (el 4 (CONJUNCTS plus_THM)))) THEN
	POP_ASSUM SUBST1_TAC THEN EXISTS_TAC "j:int" THEN
	SUBST1_TAC (num_CONV "1") THEN	
	PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL plus_ASSOC)] THEN
	REWRITE_TAC [plus_THM;LESS_0;SUB_0;SUC_SUB1;plus_ID]]]]);;

let Neg_LESS_0 = 
    prove_thm
    (`Neg_LESS_0`,
     "!i. Neg i = (i << (Int 0))",
     INDUCT_THEN int_Induct (K ALL_TAC) THEN GEN_TAC THEN
     REWRITE_TAC [Neg_DEF;Nint_less_Int;Int_less_num_less;NOT_LESS_0]);;

let Neg_minus = 
    prove_thm
    (`Neg_minus`,
     "!i j. Neg (i minus j) = (i << j)",
     REWRITE_TAC [Neg_LESS_0;minus_DEF] THEN REPEAT GEN_TAC THEN
     SUBST1_TAC (SYM(SPECL ["i:int";"j:int";"neg j"] int_LESS_plus_MONO)) THEN
     REWRITE_TAC [plus_INV]);;

let Int0_less_Exp = 
    prove_thm
    (`Int0_less_Exp`,
     "!n m. ((Int 0) << (Int ((SUC m) EXP n)))",
     CONV_TAC (REDEPTH_CONV num_CONV) THEN
     REWRITE_TAC [Int_less_num_less] THEN
     INDUCT_TAC THENL
     [REWRITE_TAC [EXP;num_CONV "1";LESS_0];
      GEN_TAC THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
      IMP_RES_TAC LESS_ADD_1 THEN 
      ASM_REWRITE_TAC [EXP;ADD_CLAUSES;num_CONV "1";LESS_0;MULT_CLAUSES]]);;

let int_Exp = 
    prove_thm
    (`int_Exp`,
     "(!n. (Int (n EXP 0) = Int 1)) /\
      (!m n.(Int (m EXP (SUC n)) = ((Int m) times (Int (m EXP n)))))",
     REWRITE_TAC [times_THM;EXP;Int_11]);;


let Int_Leq_IMP = 
     prove_thm
     (`Int_Leq_IMP`,
      "!i. ((Int 0) Leq i) ==> ?n. i = Int n",
      REWRITE_TAC [int_LESS_EQ_DEF] THEN REPEAT STRIP_TAC THENL
      [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
       EXISTS_TAC "n+1" THEN REWRITE_TAC [plus_ID];
       EXISTS_TAC "0" THEN ASM_REWRITE_TAC[]]);;

let Not_plus_less = 
    prove_thm
    (`Not_plus_less`,
     "!i n. ~(i plus (Int n)) << i",
     PURE_ONCE_REWRITE_TAC [plus_COMM] THEN REPEAT GEN_TAC THEN
     SUBST1_TAC (REWRITE_RULE [plus_ID] 
		  (SPECL ["Int n";"Int 0";"i:int"] int_LESS_plus_MONO)) THEN
     REWRITE_TAC [Int_less_num_less;NOT_LESS_0]);;

let less_EQ_NOT_Leq = 
    prove_thm
    (`less_EQ_NOT_Leq`,
     "!i j. (i << j) = (~(j Leq i))",
     REWRITE_TAC [int_LESS_EQ_DEF] THEN
     REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL int_less_CASES) THEN
     ASM_REWRITE_TAC [] THENL
     [POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
      (let th1 = REWRITE_RULE [plus_ID]
	         (SPECL ["i:int";"Int 0"] int_LESS_plus_MONO) and
           th2 = REWRITE_RULE [plus_ID]
	         (SPECL ["i:int";"j:int";"Int 0"] RIGHT_plus_CANCEL) in
       REWRITE_TAC [th1;th2;Int_11;Int_less_num_less]) THEN
       REWRITE_TAC [num_CONV "1";NOT_LESS_0;NOT_SUC;ADD_CLAUSES];
      POP_ASSUM (STRIP_THM_THEN SUBST1_TAC o MATCH_MP int_LESS_plus_1) THEN
      (let th1 = REWRITE_RULE [plus_ID]
	         (SPECL ["i:int";"Int 0"] int_LESS_plus_MONO) in
       REWRITE_TAC [th1;Int_less_num_less;NOT_LESS_0]);
      REWRITE_TAC [int_LESS_DEF;minus_DEF;plus_INV;Pos_DEF;NOT_LESS_0]]);;

let Int_less_EXP_lemma = 
    prove_thm
   (`Int_less_EXP_lemma`,
    "!n. Int(2 EXP n) << Int(2 EXP (SUC n))",
     REWRITE_TAC [Int_less_num_less;REDEPTH_CONV num_CONV "2"] THEN
     INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC [EXP] THENL
     [REWRITE_TAC [EXP;ADD_CLAUSES;MULT_CLAUSES] THEN
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
      REWRITE_TAC [ADD_CLAUSES;LESS_MONO_EQ;LESS_0];
      ASM_REWRITE_TAC [LESS_MULT_MONO]]);;

close_theory();;

quit();;