% ===================================================================== %
% FILE: mk_res_quan.ml	    DATE: 1 Aug 92	BY: Wai Wong		%
% Create the theory res_quan containing all theorems aboout		%
% restricted quantifiers.   	    					%
% ===================================================================== %

new_theory`res_quan`;;


let RESQ_FORALL = definition `bool` `RES_FORALL`;;
let RESQ_EXISTS = definition `bool` `RES_EXISTS`;;
let RESQ_SELECT = definition `bool` `RES_SELECT`;;
let RESQ_ABSTRACT = definition `bool` `RES_ABSTRACT`;;

% ===================================================================== %
% Properties of restricted quantification.                              %
% --------------------------------------------------------------------- %

% --------------------------------------------------------------------- %
% RESQ_FORALL	    	    	    					%
% --------------------------------------------------------------------- %

let RESQ_FORALL_CONJ_DIST = prove_thm(`RESQ_FORALL_CONJ_DIST`,
    "!P Q R.
     (!(i:*) :: P. (Q i /\ R i)) = (!i :: P. Q i) /\ (!i :: P. R i)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL] 
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

let RESQ_FORALL_DISJ_DIST = prove_thm(`RESQ_FORALL_DISJ_DIST`,
    "!P Q R.
     (!(i:*) :: \i. P i \/ Q i. R i) = (!i :: P. R i) /\ (!i :: Q. R i)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

let RESQ_FORALL_UNIQUE = prove_thm(`RESQ_FORALL_UNIQUE`,
    "!P j. (!(i:*) :: ($= j). P i) = P j",
    REWRITE_TAC [RESQ_FORALL] THEN BETA_TAC THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
       [DISCH_THEN (\th. ACCEPT_TAC(MP (SPEC "j:*" th) (REFL "j:*") ));
        DISCH_TAC THEN GEN_TAC THEN DISCH_THEN (\th. SUBST1_TAC (SYM th))
        THEN FIRST_ASSUM ACCEPT_TAC]);;

let RESQ_FORALL_FORALL = prove_thm(`RESQ_FORALL_FORALL`,
    "!(P:*->bool) (R:*->**->bool) x.
        (!x. !i :: P. R i x) = (!i :: P. !x. R i x)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL]
    THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let RESQ_FORALL_REORDER = prove_thm(`RESQ_FORALL_REORDER`,
    "!(P:*->bool) (Q:**->bool) (R:*->**->bool).
        (!i :: P. !j :: Q. R i j) = (!j :: Q. !i :: P. R i j)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_FORALL] THEN
    BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);;

% --------------------------------------------------------------------- %
% RESQ_EXISTS	    	    	    					%
% --------------------------------------------------------------------- %

let RESQ_EXISTS_DISJ_DIST = prove_thm(`RESQ_EXISTS_DISJ_DIST`,
    "!P Q R.
     (?(i:*) :: P. (Q i \/ R i)) = (?i :: P. Q i) \/ (?i :: P. R i)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS] 
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);;

let RESQ_DISJ_EXISTS_DIST = prove_thm(`RESQ_DISJ_EXISTS_DIST`,
    "!P Q R.
     (?(i:*) :: \i. P i \/ Q i. R i) = (?i :: P. R i) \/ (?i :: Q. R i)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS]
    THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
    THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_OR_CONV) THEN REFL_TAC);;

let RESQ_EXISTS_UNIQUE = prove_thm(`RESQ_EXISTS_UNIQUE`,
    "!P j. (?(i:*) :: ($= j). P i) = P j",
    REWRITE_TAC [RESQ_EXISTS] THEN BETA_TAC THEN REPEAT GEN_TAC
    THEN EQ_TAC THENL[
      DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN EXISTS_TAC "j:*" THEN  ASM_REWRITE_TAC[]]);;

let RESQ_EXISTS_REORDER = prove_thm(`RESQ_EXISTS_REORDER`,
    "!(P:*->bool) (Q:**->bool) (R:*->**->bool).
        (?i :: P. ?j :: Q. R i j) = (?j :: Q. ?i :: P. R i j)",
    REPEAT STRIP_TAC THEN REWRITE_TAC [RESQ_EXISTS] THEN BETA_TAC
    THEN EQ_TAC THEN DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THENL[
      EXISTS_TAC "x':**" THEN CONJ_TAC THENL[
    	ALL_TAC; EXISTS_TAC"x:*" THEN CONJ_TAC];
      EXISTS_TAC "x':*" THEN CONJ_TAC THENL[
    	ALL_TAC; EXISTS_TAC"x:**" THEN CONJ_TAC]]
    THEN FIRST_ASSUM ACCEPT_TAC);;


close_theory();;

