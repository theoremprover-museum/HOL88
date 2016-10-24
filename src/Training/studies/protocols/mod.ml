% NOW runs in HOL88  30/v/89 RCO %
% NOW runs in HOL12  19/3/91 RCO %
% FILE		: mod.ml						%
% DESCRIPTION   : Theory of the Mod operator.				%
%		 							%
% READS FILES	: da.th							%
% WRITES FILES  : mod.th						%
%									%
% AUTHOR	: T.F. Melham						%
% DATE		: 86.02.01						%

% Create the new theory "mod.th"					%
new_theory `mod`;;

% Parent theory is "da.th" --- the division algorithm			%
new_parent `da`;;

% Fetch theorems from da.th						%
let Da = theorem `da` `Da` and
    Quotient_Unique = theorem `da` `Quotient_Unique` and
    Remainder_Unique = theorem `da` `Remainder_Unique`;;

% Define the Mod operator.						%
let Mod = 
    new_infix_definition
    (`Mod`,
     "Mod k n = @r. ?q. (k = (q * n) + r) /\ r < n");;

let Div = 
    new_infix_definition
    (`Div`,
     "Div k n = @q. (k = (q * n) + (k Mod n))");;

let Da_Mod_thm = 
    prove_thm
    (`Da_Mod_thm`,
     "!n. ~(n=0) ==> !k. ?q. (k = ((q * n) + (k Mod n))) /\ ((k Mod n) < n)",
     REPEAT STRIP_TAC THEN
     POP_ASSUM (ASSUME_TAC o MP (SPEC_ALL Da)) THEN
     REWRITE_TAC [Mod] THEN
     CONV_TAC SELECT_CONV THEN
     POP_ASSUM ACCEPT_TAC);;


let Da_Div_thm = 
    prove_thm
    (`Da_Div_thm`,
     "!n. ~(n=0) ==> !k. (k = (((k Div n) * n) + (k Mod n)))",
     REPEAT STRIP_TAC THEN REWRITE_TAC [Div] THEN
     CONV_TAC SELECT_CONV THEN
     IMP_RES_TAC Da_Mod_thm THEN 
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL) THEN
     EXISTS_TAC "q:num" THEN
     FIRST_ASSUM ACCEPT_TAC);;


let Div_less_eq = 
    prove_thm
    (`Div_less_eq`,
     "!n. ~(n=0) ==> !k. (k Div n) <= k",
     REPEAT STRIP_TAC THEN 
     IMP_RES_TAC Da_Div_thm THEN
     POP_ASSUM (\th. SUBST_OCCS_TAC [[2],SPEC_ALL th]) THEN
     STRIP_ASSUME_TAC (SPEC "n:num" num_CASES) THENL
     [RES_TAC;
      POP_ASSUM (\th. SUBST_OCCS_TAC [[3],th]) THEN
      REWRITE_TAC [MULT_CLAUSES] THEN
      REWRITE_TAC [SYM(SPEC_ALL ADD_ASSOC)] THEN
      MATCH_ACCEPT_TAC LESS_EQ_ADD]);;

let Mod_Less = 
    prove_thm
    (`Mod_Less`,
     "!n. ~(n=0) ==> !k. (k Mod n) < n",
     REPEAT STRIP_TAC THEN IMP_RES_TAC Da_Mod_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL));;

let Div_thm = 
    prove_thm
    (`Div_thm`,
     "!n r. r < n ==> !q. (((q * n) + r) Div n = q)",
     INDUCT_TAC THENL
     [REWRITE_TAC [NOT_LESS_0];
      POP_ASSUM (K ALL_TAC) THEN REPEAT STRIP_TAC THEN
      ASSUME_TAC (SPEC "((q * (SUC n))+r)" (MP (SPEC "SUC n" Mod_Less)
      		           (SPEC_ALL NOT_SUC))) THEN
      POP_ASSUM \th1. (POP_ASSUM \th2.
         (ASSUME_TAC (MATCH_MP Quotient_Unique (CONJ th1 th2)))) THEN
      POP_ASSUM (MATCH_MP_TAC o (SPECL ["((q * (SUC n))+r) Div (SUC n)";
      				      "q:num"; "(q * (SUC n))+r"])) THEN
      REWRITE_TAC [SYM(SPEC_ALL(MP (SPEC "SUC n" Da_Div_thm) 
      				   (SPEC_ALL NOT_SUC)))]]);;

let Mod_One = 
    prove_thm
    (`Mod_One`,
     "!k. (k Mod 1) = 0",
     CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN
     MP_TAC (REWRITE_RULE [NOT_SUC] (SPEC "SUC 0" Mod_Less)) THEN
     REWRITE_TAC [LESS_THM;NOT_LESS_0]);;

let LESS_ADD_SUC = GEN_ALL (REWRITE_RULE [LESS_0;ADD_CLAUSES] 
                   (SYM (SPECL ["0";"SUC p";"k:num"] LESS_MONO_ADD_EQ)));;

let lemma = TAC_PROOF(([],"(0*(SUC(k+p))) + k = k"),
    REWRITE_TAC[MULT_CLAUSES;ADD_CLAUSES]);;

let Less_Mod = 
    prove_thm
    (`Less_Mod`,
     "!n k. k < n ==> ((k Mod n) = k)",
     REPEAT GEN_TAC THEN 
     DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [ADD_CLAUSES;num_CONV "1"] THEN
     ASSUME_TAC (REWRITE_RULE [NOT_SUC] (SPEC "SUC (k+p)" Da_Mod_thm)) THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "k:num") THEN
     ASSUME_TAC (REWRITE_RULE[ADD_CLAUSES]
                (SPECL ["k:num";"p:num"] LESS_ADD_SUC)) THEN
     MP_TAC (SPECL ["SUC(k+p)";"k:num";"k Mod (SUC(k+p))"] 
             Remainder_Unique) THEN
     UNDISCH_TAC "k = (q * (SUC(k + p))) + (k Mod (SUC(k + p)))" 
     THEN DISCH_TAC THEN 
     POP_ASSUM(\th. ASSUME_TAC (TRANS lemma th)) THEN
     ASM_REWRITE_TAC[] THEN
     POP_ASSUM(\th. ASSUME_TAC 
        (EXISTS ("?q2. (0 * (SUC(k + p))) + k =
        (q2 * (SUC(k + p))) + (k Mod (SUC(k + p)))","q:num") 
        th)) THEN
     POP_ASSUM(\th. ASSUME_TAC 
        (EXISTS ("?q1. (?q2. (q1 * (SUC(k + p))) + k =
        (q2 * (SUC(k + p))) + (k Mod (SUC(k + p))))","0") 
        th)) THEN
    POP_ASSUM(\th. REWRITE_TAC[th]) THEN DISCH_TAC THEN
    POP_ASSUM(\th. REWRITE_TAC[SYM th]) );;

let Mod_EQ_0 = 
    prove_thm
    (`Mod_EQ_0`,
     "!k. ~(k = 0) ==> !n. ((n * k) Mod k) = 0",
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC Da_Mod_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "n * k") THEN
     STRIP_ASSUME_TAC (SPEC "k:num" LESS_0_CASES) THENL
     [POP_ASSUM (STRIP_ASSUME_TAC o SYM) THEN RES_TAC;
      MP_TAC (SPECL ["k:num";"0";"(n*k) Mod k"] 
              Remainder_Unique) THEN
      UNDISCH_TAC "n * k = (q * k) + ((n * k) Mod k)" THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN 
      POP_ASSUM(\th. ASSUME_TAC 
        (EXISTS ("?q2. n * k = (q2 * k) + ((n * k) Mod k)",
                 "q:num") th)) THEN
      POP_ASSUM(\th. ASSUME_TAC 
        (EXISTS ("?q1.(?q2. q1 * k = (q2 * k) + ((n * k) Mod k))",
                 "n:num") th)) THEN
      POP_ASSUM(\th. REWRITE_TAC[th]) THEN DISCH_TAC THEN
      POP_ASSUM(ASSUME_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

let Zero_Mod = 
    prove_thm
    (`Zero_Mod`,
     "!k. ~(k = 0) ==> ((0 Mod k) = 0)",
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC Mod_EQ_0 THEN
     POP_ASSUM (MP_TAC o SPEC "0") THEN
     REWRITE_TAC [MULT_CLAUSES]);;

let Mod_Rem_thm = 
    prove_thm
    (`Mod_Rem_thm`,
     "!n k. k < n ==> !m. (((m * n) + k) Mod n) = k",
     REPEAT GEN_TAC THEN 
     DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
     REWRITE_TAC [ADD_CLAUSES;num_CONV "1"] THEN
     ASSUME_TAC (REWRITE_RULE [NOT_SUC] (SPEC "SUC (k+p)" Da_Mod_thm)) THEN
     STRIP_TAC THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "((m * SUC(k + p)))+k") THEN
     ASSUME_TAC (REWRITE_RULE [ADD_CLAUSES] 
	        (SPECL ["k:num";"p:num"] LESS_ADD_SUC)) THEN
     MP_TAC (SPECL ["SUC(k+p)";"k:num";
                    "((m*(SUC(k+p)))+k) Mod (SUC(k+p))"] 
             Remainder_Unique) THEN
     UNDISCH_TAC "(m * (SUC(k + p))) + k =
       (q * (SUC(k + p))) + (((m * (SUC(k + p))) + k) Mod 
       (SUC(k + p)))"  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(\th. ASSUME_TAC
      (EXISTS ("?q2. (m * (SUC(k + p))) + k =
               (q2 * (SUC(k + p))) + 
               (((m * (SUC(k + p))) + k) Mod (SUC(k + p)))",
      "q:num") th)) THEN
    POP_ASSUM(\th. ASSUME_TAC
      (EXISTS ("?q1. ?q2. (q1 * (SUC(k + p))) + k =
               (q2 * (SUC(k + p))) + 
               (((m * (SUC(k + p))) + k) Mod (SUC(k + p)))",
      "m:num") th)) THEN
   POP_ASSUM(\th. REWRITE_TAC[th]) THEN DISCH_TAC THEN
   POP_ASSUM(ASSUME_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC);;

let Mod_thm  = 
    prove_thm
    (`Mod_thm`,
     "!k. ~(k = 0) ==> !n r. (((n * k) + r) Mod k) = (r Mod k)",
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC Da_Mod_thm THEN
     POP_ASSUM (STRIP_ASSUME_TAC o SPEC "r:num") THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (\th. SUBST_OCCS_TAC [[1],th]) THEN
     REWRITE_TAC [ADD_ASSOC;SYM(SPEC_ALL RIGHT_ADD_DISTRIB)] THEN
     IMP_RES_TAC Mod_Less THEN
     POP_ASSUM (ASSUME_TAC o SPEC "r:num") THEN
     IMP_RES_TAC Mod_Rem_thm THEN
     POP_ASSUM (ASSUME_TAC o SPEC "n+q") THEN
     POP_ASSUM MATCH_ACCEPT_TAC);;

let Add_Mod = 
    prove_thm
    (`Add_Mod`,
     "!k. ~(k = 0) ==> !n m.(((n Mod k) + (m Mod k)) Mod k) = ((n+m) Mod k)",
     REPEAT STRIP_TAC THEN
     IMP_RES_TAC Mod_thm THEN
     IMP_RES_TAC Da_Mod_thm THEN
     POP_ASSUM (\th. MAP_EVERY (STRIP_ASSUME_TAC o uncurry SPEC) 
               (["m:num",th;"n:num",th])) THEN 
     POP_ASSUM (\thm. POP_ASSUM (\th. SUBST_OCCS_TAC [[2],th])) THEN
     FILTER_ASM_REWRITE_TAC (is_forall) [SYM(SPEC_ALL ADD_ASSOC)] THEN
     PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
     POP_ASSUM (\thm. POP_ASSUM (\th. SUBST_OCCS_TAC [[2],th])) THEN
     FILTER_ASM_REWRITE_TAC (is_forall) [SYM(SPEC_ALL ADD_ASSOC)]);;

let Mod_Mod = 
    prove_thm
    (`Mod_Mod`,
     "!k. (~(k = 0)) ==> (!n. (n Mod k) Mod k = (n Mod k))",
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC Less_Mod THEN 
     IMP_RES_TAC Mod_Less THEN
     ASM_REWRITE_TAC []);;


% Close the theory "mod.th".%
close_theory();;

quit();;
